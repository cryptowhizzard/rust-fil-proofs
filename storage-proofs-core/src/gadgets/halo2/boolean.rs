use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::AssignedCell,
    plonk::{Assigned, Error, Expression, Selector},
};

// Returns `1` if both `b0` and `b1` are `1`.
//
// Assumes `bit_0` and `bit_1` are already boolean constrained.
#[inline]
pub fn and<F: FieldExt>(bit_0: Expression<F>, bit_1: Expression<F>) -> Expression<F> {
    bit_0 * bit_1
}

// Returns `1` if both `b0` and `b1` are `0`.
//
// Assumes `bit_0` and `bit_1` are already boolean constrained.
#[inline]
pub fn nor<F: FieldExt>(bit_0: Expression<F>, bit_1: Expression<F>) -> Expression<F> {
    (Expression::Constant(F::one()) - bit_0) * (Expression::Constant(F::one()) - bit_1)
}

pub type AssignedBit<F> = AssignedCell<Bit, F>;

#[derive(Clone, Debug)]
pub struct Bit(pub bool);

impl<F: FieldExt> From<&Bit> for Assigned<F> {
    fn from(bit: &Bit) -> Self {
        if bit.0 {
            F::one().into()
        } else {
            F::zero().into()
        }
    }
}

impl From<bool> for Bit {
    fn from(bit: bool) -> Self {
        Bit(bit)
    }
}

/*
#[derive(Clone, Debug)]
struct LeBitsConfig<F: FieldExt> {
    advice: [Column<Advice>; 8],
    s_le_bits: Selector,
    _f: PhantomData<F>,
}

struct LeBitsChip<F: FieldExt> {
    config: LeBitsConfig<F>,
}

impl<F: FieldExt> LeBitsChip<F> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 8],
    ) -> LeBitsConfig<F> {
        const FIELD_SIZE: usize = 255;
        const NUM_ROWS: usize = 32;

        meta.enable_equality(advice[0]);

        let s_le_bits= meta.selector();

        meta.create_gate("le_bits", |meta| {
            let s_le_bits = meta.query_selector(s_le_bits);
            let val = meta.query_advice(advice[0], Rotation::cur());

            let bits = 
        });

        LeBitsConfig {
            advice,
            s_le_bits,
            _f: PhantomData,
        }
    }
}

pub fn le_bits<F: FieldExt>(
    config: &LeBitsConfig,
    region: &mut Region<'_, F>,
    offset: usize,
    val: AssignedCell<F, F>,
) -> Result<Vec<AssignedCell<F, F>>, Error> {

}
*/

#[cfg(test)]
mod tests {
    use super::*;

    use std::convert::TryInto;

    use ff::{Field, PrimeFieldBits};
    use halo2_gadgets::utilities::decompose_running_sum::RunningSumConfig;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        pasta::Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem},
    };
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use crate::TEST_SEED;

    const FIELD_BITS: usize = 255;
    const WINDOW_BITS: usize = 3;
    const NUM_WINDOWS: usize = FIELD_BITS / WINDOW_BITS;

    #[derive(Clone, Debug)]
    struct MyConfig<F>
    where
        F: FieldExt + PrimeFieldBits,
    {

        // One column for a field element and eight columns for each of its bits.
        advice: [Column<Advice>; 9],
        // Decompose each preimage element into a byte, i.e. a value in `0..2^3`.
        bytes_decomp: RunningSumConfig<F, 3>,
    }

    struct MyCircuit<F>
    where
        F: FieldExt + PrimeFieldBits,
    {
        preimage: Vec<Option<F>>,
    }

    impl<F> Circuit<F> for MyCircuit<F>
    where
        F: FieldExt + PrimeFieldBits,
    {
        type Config = MyConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            MyCircuit {
                preimage: vec![None; self.preimage.len()],
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice: [Column<Advice>; 9] = (0..9)
                .map(|_| meta.advice_column())
                .collect::<Vec<Column<Advice>>>()
                .try_into()
                .unwrap();

            // Running sum chip requires one fixed column.
            let fixed = meta.fixed_column();
            meta.enable_constant(fixed);
            let s_bytes_decomp = meta.selector();
            let bytes_decomp = RunningSumConfig::configure(meta, s_bytes_decomp, advice[0]);

            MyConfig {
                advice,
                bytes_decomp,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "sha256 preimage",
                |mut region| {
                    let mut offset = 0;

                    let mut preimage_bits = Vec::<Option<bool>>::with_capacity(NUM_WINDOWS);

                    let eight = F::from(1 << WINDOW_BITS);

                    for (i, elem_opt) in self.preimage.iter().enumerate() {
                        // A vector containing the running sum elements `z_0, ..., z_32`.
                        let zs = config.bytes_decomp.witness_decompose(
                            &mut region,
                            offset,
                            elem_opt.clone(),
                            true,
                            255,
                            85,
                        )?;

                        if zs.iter().any(|z_i| z_i.value().is_none()) {
                            preimage_bits.extend_from_slice(&[None; NUM_WINDOWS * WINDOW_BITS]);
                        } else {
                            for window in zs.windows(2) {
                                let z_cur = window[0].value().unwrap();
                                let z_next = window[1].value().unwrap();
                                let k_cur = *z_cur - eight * z_next;
                                assert!(k_cur < eight);
                                let repr = k_cur.to_repr().as_ref()[0];
                                for bit_index in 0..WINDOW_BITS {
                                    preimage_bits.push(Some((repr >> bit_index) & 1 == 1));
                                }
                            }
                        }

                        // One row for the preimage element and one row per 3-bit window.
                        offset += NUM_WINDOWS + 1;
                    }

                    if !preimage_bits.iter().any(|opt| opt.is_none()) {
                        let expected_bits: Vec<Option<bool>> = self.preimage
                            .iter()
                            .flat_map(|opt| {
                                opt.unwrap().to_le_bits().into_iter().take(FIELD_BITS).map(Some)
                            })
                            .collect();
                        assert_eq!(preimage_bits, expected_bits);
                    }

                    Ok(())
                },
            )
        }
    }

    #[test]
    fn test_halo2_sha256_preimage() {
        let mut rng = XorShiftRng::from_seed(TEST_SEED);
        let preimage = vec![Some(Fp::random(&mut rng))];
        let circ = MyCircuit { preimage };
        let prover = MockProver::run(9, &circ, vec![]).unwrap();
    }
}
