use std::marker::PhantomData;

use filecoin_hashers::{ColumnSpec, PoseidonArity};
use generic_array::typenum::{U2, U4, U8};
use halo2_gadgets::utilities::ternary;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use crate::gadgets::halo2::{and, nor, AssignedBit};

// Returns `a` if `bit` is set, otherwise returns `b`.
//
// Assumes `bit` is already boolean constrained.
#[inline]
pub fn pick<F: FieldExt>(bit: Expression<F>, a: Expression<F>, b: Expression<F>) -> Expression<F> {
    ternary(bit, a, b)
}

#[derive(Clone, Debug)]
pub struct InsertConfig {
    uninserted: Vec<Column<Advice>>,
    value: Column<Advice>,
    index_bits: Vec<Column<Advice>>,
    inserted: Vec<Column<Advice>>,
    s_insert: Selector,
}

pub struct InsertChip<F, A>
where
    F: FieldExt,
    A: PoseidonArity<F>,
{
    config: InsertConfig,
    _f: PhantomData<F>,
    _a: PhantomData<A>,
}

impl<F, A> InsertChip<F, A>
where
    F: FieldExt,
    A: PoseidonArity<F>,
{
    pub fn construct(config: InsertConfig) -> Self {
        InsertChip {
            config,
            _f: PhantomData,
            _a: PhantomData,
        }
    }

    pub fn column_spec() -> ColumnSpec {
        let arity = A::to_usize();
        let index_bit_len = arity.trailing_zeros() as usize;
        ColumnSpec {
            // The index bits, insertion value, and inserted array elements must be equality
            // constrained.
            advice_eq: index_bit_len + 1 + arity,
            advice_neq: arity - 1,
            fixed_eq: 0,
            fixed_neq: 0,
        }
    }

    // # Side Effects
    //
    // - All `io` columns will be equality constrained.
    //
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        io: &[Column<Advice>],
        extra: &[Column<Advice>],
    ) -> InsertConfig {
        let arity = A::to_usize();
        assert!([2, 4, 8].contains(&arity));

        let num_cols = Self::column_spec();
        assert_eq!(io.len(), num_cols.advice_eq);
        assert_eq!(extra.len(), num_cols.advice_neq);

        for col in io.iter() {
            meta.enable_equality(*col);
        }

        let index_bit_len = arity.trailing_zeros() as usize;
        let index_bits = io[..index_bit_len].to_vec();
        let value = io[index_bit_len].clone();
        let inserted = io[index_bit_len + 1..].to_vec();
        let uninserted = extra.to_vec();

        let s_insert = meta.selector();

        match arity {
            2 => {
                meta.create_gate("insert_2", |meta| {
                    let s_insert = meta.query_selector(s_insert);

                    let a = meta.query_advice(value, Rotation::cur());
                    let b = meta.query_advice(uninserted[0], Rotation::cur());

                    let bit = meta.query_advice(index_bits[0], Rotation::cur());

                    let out_0 = meta.query_advice(inserted[0], Rotation::cur());
                    let out_1 = meta.query_advice(inserted[1], Rotation::cur());

                    let pick_0 = pick(bit.clone(), b.clone(), a.clone());
                    let pick_1 = pick(bit, a, b);

                    vec![
                        s_insert.clone() * (out_0 - pick_0),
                        s_insert * (out_1 - pick_1),
                    ]
                });
            }
            4 => {
                meta.create_gate("insert_4", |meta| {
                    let s_insert = meta.query_selector(s_insert);

                    let a = meta.query_advice(value, Rotation::cur());
                    let b = meta.query_advice(uninserted[0], Rotation::cur());
                    let c = meta.query_advice(uninserted[1], Rotation::cur());
                    let d = meta.query_advice(uninserted[2], Rotation::cur());

                    let b0 = meta.query_advice(index_bits[0], Rotation::cur());
                    let b1 = meta.query_advice(index_bits[1], Rotation::cur());

                    let out_0 = meta.query_advice(inserted[0], Rotation::cur());
                    let out_1 = meta.query_advice(inserted[1], Rotation::cur());
                    let out_2 = meta.query_advice(inserted[2], Rotation::cur());
                    let out_3 = meta.query_advice(inserted[3], Rotation::cur());

                    let pick_0 = {
                        let tmp = pick(b0.clone(), b.clone(), a.clone());
                        pick(b1.clone(), b.clone(), tmp)
                    };

                    let pick_1 = {
                        let tmp = pick(b0.clone(), a.clone(), b);
                        pick(b1.clone(), c.clone(), tmp)
                    };

                    let pick_2 = {
                        let tmp = pick(b0.clone(), d.clone(), a.clone());
                        pick(b1.clone(), tmp, c)
                    };

                    let pick_3 = {
                        let tmp = pick(b0, a, d.clone());
                        pick(b1, tmp, d)
                    };

                    vec![
                        s_insert.clone() * (out_0 - pick_0),
                        s_insert.clone() * (out_1 - pick_1),
                        s_insert.clone() * (out_2 - pick_2),
                        s_insert * (out_3 - pick_3),
                    ]
                });
            }
            8 => {
                meta.create_gate("insert_8", |meta| {
                    let s_insert = meta.query_selector(s_insert);

                    let a = meta.query_advice(value, Rotation::cur());
                    let b = meta.query_advice(uninserted[0], Rotation::cur());
                    let c = meta.query_advice(uninserted[1], Rotation::cur());
                    let d = meta.query_advice(uninserted[2], Rotation::cur());
                    let e = meta.query_advice(uninserted[3], Rotation::cur());
                    let f = meta.query_advice(uninserted[4], Rotation::cur());
                    let g = meta.query_advice(uninserted[5], Rotation::cur());
                    let h = meta.query_advice(uninserted[6], Rotation::cur());

                    let b0 = meta.query_advice(index_bits[0], Rotation::cur());
                    let b1 = meta.query_advice(index_bits[1], Rotation::cur());
                    let b2 = meta.query_advice(index_bits[2], Rotation::cur());

                    let out_0 = meta.query_advice(inserted[0], Rotation::cur());
                    let out_1 = meta.query_advice(inserted[1], Rotation::cur());
                    let out_2 = meta.query_advice(inserted[2], Rotation::cur());
                    let out_3 = meta.query_advice(inserted[3], Rotation::cur());
                    let out_4 = meta.query_advice(inserted[4], Rotation::cur());
                    let out_5 = meta.query_advice(inserted[5], Rotation::cur());
                    let out_6 = meta.query_advice(inserted[6], Rotation::cur());
                    let out_7 = meta.query_advice(inserted[7], Rotation::cur());

                    let b0_and_b1 = and(b0.clone(), b1.clone());
                    let b0_nor_b1 = nor(b0.clone(), b1.clone());

                    let tmp_0 = pick(b0_nor_b1.clone(), a.clone(), b.clone());
                    let pick_0 = pick(b2.clone(), b.clone(), tmp_0);
                    
                    let tmp_1_0 = pick(b0.clone(), a.clone(), b.clone());
                    let tmp_1_1 = pick(b1.clone(), c.clone(), tmp_1_0);
                    let pick_1 = pick(b2.clone(), c.clone(), tmp_1_1);

                    let tmp_2_0 = pick(b0.clone(), d.clone(), a.clone());
                    let tmp_2_1 = pick(b1.clone(), tmp_2_0, c.clone());
                    let pick_2 = pick(b2.clone(), d.clone(), tmp_2_1);

                    let tmp_3 = pick(b0_and_b1.clone(), a.clone(), d.clone());
                    let pick_3 = pick(b2.clone(), e.clone(), tmp_3);

                    let tmp_4 = pick(b0_nor_b1, a.clone(), f.clone());
                    let pick_4 = pick(b2.clone(), tmp_4, e.clone());

                    let tmp_5_0 = pick(b0.clone(), a.clone(), f.clone());
                    let tmp_5_1 = pick(b1.clone(), g.clone(), tmp_5_0);
                    let pick_5 = pick(b2.clone(), tmp_5_1, f);

                    let tmp_6_0 = pick(b0.clone(), h.clone(), a.clone());
                    let tmp_6_1 = pick(b1.clone(), tmp_6_0, g.clone());
                    let pick_6 = pick(b2.clone(), tmp_6_1, g);

                    let tmp_7 = pick(b0_and_b1, a.clone(), h.clone());
                    let pick_7 = pick(b2.clone(), tmp_7, h);

                    vec![
                        s_insert.clone() * (out_0 - pick_0),
                        s_insert.clone() * (out_1 - pick_1),
                        s_insert.clone() * (out_2 - pick_2),
                        s_insert.clone() * (out_3 - pick_3),
                        s_insert.clone() * (out_4 - pick_4),
                        s_insert.clone() * (out_5 - pick_5),
                        s_insert.clone() * (out_6 - pick_6),
                        s_insert * (out_7 - pick_7),
                    ]
                });
            }
            _ => unimplemented!(),
        };

        InsertConfig {
            uninserted,
            index_bits,
            value,
            inserted,
            s_insert,
        }
    }

    pub fn insert<T>(
        &self,
        mut layouter: impl Layouter<F>,
        uninserted: &[Option<T>],
        value: &AssignedCell<T, F>,
        index_bits: &[AssignedBit<F>],
    ) -> Result<Vec<AssignedCell<T, F>>, Error>
    where
        T: Clone,
        for<'t> Assigned<F>: From<&'t T>,
    {
        let arity = A::to_usize();
        assert_eq!(uninserted.len(), arity - 1);

        let index_bit_len = arity.trailing_zeros() as usize;
        assert_eq!(index_bits.len(), index_bit_len);

        let index_opt: Option<usize> = index_bits
            .iter()
            .enumerate()
            .map(|(i, assigned_bit)| assigned_bit.value().map(|bit| (bit.0 as usize) << i))
            .reduce(|acc, opt| acc.zip(opt).map(|(acc, val)| acc + val))
            .unwrap();

        let mut inserted: Vec<Option<&T>> = uninserted.iter().map(|opt| opt.as_ref()).collect();
        inserted.insert(index_opt.unwrap_or(0), value.value());

        layouter.assign_region(
            || format!("insert_{}", arity),
            |mut region| {
                let row = 0;

                self.config.s_insert.enable(&mut region, row)?;

                // Copy the insertion index.
                for i in 0..index_bit_len {
                    index_bits[i].copy_advice(
                        || format!("index bit {}", i),
                        &mut region,
                        self.config.index_bits[i],
                        row,
                    )?;
                }

                // Copy insertion value.
                value.copy_advice(|| "value", &mut region, self.config.value, row)?;

                // Allocate uninserted array.
                for (i, opt) in uninserted.iter().enumerate() {
                    region.assign_advice(
                        || format!("uninserted {}", i),
                        self.config.uninserted[i],
                        row,
                        || opt.clone().ok_or(Error::Synthesis),
                    )?;
                }

                // Allocate the inserted array.
                inserted
                    .iter()
                    .enumerate()
                    .map(|(i, opt)| {
                        region.assign_advice(
                            || format!("inserted {}", i),
                            self.config.inserted[i],
                            row,
                            || opt.cloned().ok_or(Error::Synthesis),
                        )
                    })
                    .collect()
            },
        )
    }

    pub fn assign_value_then_insert<T>(
        &self,
        mut layouter: impl Layouter<F>,
        uninserted: &[Option<T>],
        value: &Option<T>,
        index_bits: &[AssignedBit<F>],
    ) -> Result<Vec<AssignedCell<T, F>>, Error>
    where
        T: Clone,
        for<'t> Assigned<F>: From<&'t T>,
    {
        let arity = A::to_usize();
        assert_eq!(uninserted.len(), arity - 1);

        let index_bit_len = arity.trailing_zeros() as usize;
        assert_eq!(index_bits.len(), index_bit_len);

        let index_opt: Option<usize> = index_bits
            .iter()
            .enumerate()
            .map(|(i, assigned_bit)| assigned_bit.value().map(|bit| (bit.0 as usize) << i))
            .reduce(|acc, opt| acc.zip(opt).map(|(acc, val)| acc + val))
            .unwrap();

        let mut inserted: Vec<Option<&T>> = uninserted.iter().map(|opt| opt.as_ref()).collect();
        inserted.insert(index_opt.unwrap_or(0), value.as_ref());

        layouter.assign_region(
            || format!("insert_{}", arity),
            |mut region| {
                let row = 0;

                self.config.s_insert.enable(&mut region, row)?;

                // Copy the insertion index.
                for i in 0..index_bit_len {
                    index_bits[i].copy_advice(
                        || format!("index bit {}", i),
                        &mut region,
                        self.config.index_bits[i],
                        row,
                    )?;
                }

                // Allocate insertion value.
                region.assign_advice(
                    || "value",
                    self.config.value,
                    row,
                    || value.clone().ok_or(Error::Synthesis),
                )?;

                // Allocate uninserted array.
                for (i, opt) in uninserted.iter().enumerate() {
                    region.assign_advice(
                        || format!("uninserted {}", i),
                        self.config.uninserted[i],
                        row,
                        || opt.clone().ok_or(Error::Synthesis),
                    )?;
                }

                // Allocate inserted array.
                inserted
                    .iter()
                    .enumerate()
                    .map(|(i, opt)| {
                        region.assign_advice(
                            || format!("inserted {}", i),
                            self.config.inserted[i],
                            row,
                            || opt.cloned().ok_or(Error::Synthesis),
                        )
                    })
                    .collect()
            },
        )
    }
}

pub fn insert<T, F>(
    layouter: impl Layouter<F>,
    config: InsertConfig,
    uninserted: &[Option<T>],
    value: &AssignedCell<T, F>,
    index_bits: &[AssignedBit<F>],
) -> Result<Vec<AssignedCell<T, F>>, Error>
where
    T: Clone,
    for<'t> Assigned<F>: From<&'t T>,
    F: FieldExt,
{
    let arity = uninserted.len() + 1;
    match arity {
        2 => InsertChip::<F, U2>::construct(config).insert(layouter, uninserted, value, index_bits),
        4 => InsertChip::<F, U4>::construct(config).insert(layouter, uninserted, value, index_bits),
        8 => InsertChip::<F, U8>::construct(config).insert(layouter, uninserted, value, index_bits),
        _ => unimplemented!("arity-{} insert chip is not yet supported", arity),
    }
}

pub fn assign_value_then_insert<T, F>(
    layouter: impl Layouter<F>,
    config: InsertConfig,
    uninserted: &[Option<T>],
    value: &Option<T>,
    index_bits: &[AssignedBit<F>],
) -> Result<Vec<AssignedCell<T, F>>, Error>
where
    T: Clone,
    for<'t> Assigned<F>: From<&'t T>,
    F: FieldExt,
{
    let arity = uninserted.len() + 1;
    match arity {
        2 => InsertChip::<F, U2>::construct(config)
            .assign_value_then_insert(layouter, uninserted, value, index_bits),
        4 => InsertChip::<F, U4>::construct(config)
            .assign_value_then_insert(layouter, uninserted, value, index_bits),
        8 => InsertChip::<F, U8>::construct(config)
            .assign_value_then_insert(layouter, uninserted, value, index_bits),
        _ => unimplemented!("arity-{} insert chip is not yet supported", arity),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use generic_array::typenum::{U2, U4, U8};
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        pasta::{Fp, Fq},
        plonk::Circuit,
    };

    use crate::gadgets::halo2::Bit;

    #[derive(Clone, Debug)]
    struct MyConfig {
        insert: InsertConfig,
        advice_eq: Vec<Column<Advice>>,
    }

    struct MyCircuit<F, A>
    where
        F: FieldExt,
        A: PoseidonArity<F>,
    {
        uninserted: Vec<Option<F>>,
        value: Option<F>,
        index_bits: Vec<Option<bool>>,
        _a: PhantomData<A>,
    }

    impl<F, A> Circuit<F> for MyCircuit<F, A>
    where
        F: FieldExt,
        A: PoseidonArity<F>,
    {
        type Config = MyConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            let arity = A::to_usize();
            let index_bit_len = arity.trailing_zeros() as usize;
            MyCircuit {
                uninserted: vec![None; arity - 1],
                value: None,
                index_bits: vec![None; index_bit_len],
                _a: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let num_cols = InsertChip::<F, A>::column_spec();

            let advice_eq: Vec<Column<Advice>> = (0..num_cols.advice_eq)
                .map(|_| meta.advice_column())
                .collect();

            let advice_neq: Vec<Column<Advice>> = (0..num_cols.advice_neq)
                .map(|_| meta.advice_column())
                .collect();

            let insert = InsertChip::<F, A>::configure(meta, &advice_eq, &advice_neq);

            MyConfig {
                insert,
                advice_eq,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = InsertChip::<F, A>::construct(config.insert.clone());

            let (value, index_bits) = layouter.assign_region(
                || "value",
                |mut region| {
                    let row = 0;

                    // Allocate insertion value.
                    let value = region.assign_advice(
                        || "value",
                        config.advice_eq[0],
                        row,
                        || self.value.ok_or(Error::Synthesis),
                    )?;

                    // Allocate insertion index.
                    let index_bits = self.index_bits
                        .iter()
                        .enumerate()
                        .map(|(i, opt)| {
                            region.assign_advice(
                                || format!("index bit {}", i),
                                config.advice_eq[1 + i],
                                row,
                                || opt.map(Bit).ok_or(Error::Synthesis),
                            )
                        })
                        .collect::<Result<Vec<AssignedBit<F>>, Error>>()?;

                    Ok((value, index_bits))
                },
            )?;

            let inserted = chip.insert(
                layouter.namespace(|| "insert"),
                &self.uninserted,
                &value,
                &index_bits,
            )?;

            let index = if self.index_bits.iter().any(|opt| opt.is_none()) {
                0
            } else {
                self.index_bits
                    .iter()
                    .enumerate()
                    .map(|(i, opt)| (opt.unwrap() as usize) << i)
                    .reduce(|acc, next| acc + next)
                    .unwrap()
            };

            let mut expected = self.uninserted.clone();
            expected.insert(index, self.value);
            assert_eq!(
                inserted.iter().map(|asn| asn.value()).collect::<Vec<Option<&F>>>(),
                expected.iter().map(|opt| opt.as_ref()).collect::<Vec<Option<&F>>>(),
            );

            Ok(())
        }
    }

    impl<F, A> MyCircuit<F, A>
    where
        F: FieldExt,
        A: PoseidonArity<F>,
    {
        fn with_witness(uninserted: &[F], value: F, index: usize) -> Self {
            let arity = A::to_usize();
            assert_eq!(uninserted.len(), arity - 1);

            let index_bit_len = arity.trailing_zeros() as usize;

            let index_bits: Vec<Option<bool>> = (0..index_bit_len)
                .map(|i| Some((index >> i) & 1 == 1))
                .collect();

            MyCircuit {
                uninserted: uninserted.iter().map(|elem| Some(*elem)).collect(),
                value: Some(value),
                index_bits,
                _a: PhantomData,
            }
        }
    }

    fn test_halo2_insert_inner<F, A>()
    where
        F: FieldExt,
        A: PoseidonArity<F>,
    {
        let arity = A::to_usize();
        let value = F::from(55);
        let uninserted: Vec<F> = (0..arity - 1).map(|i| F::from(i as u64)).collect();
        for i in 0..arity {
            let circ = MyCircuit::<F, A>::with_witness(&uninserted, value.clone(), i);
            let prover = MockProver::run(3, &circ, vec![]).unwrap();
            assert!(prover.verify().is_ok());
        }
    }

    #[test]
    fn test_halo2_insert() {
        test_halo2_insert_inner::<Fp, U2>();
        test_halo2_insert_inner::<Fp, U4>();
        test_halo2_insert_inner::<Fp, U8>();

        test_halo2_insert_inner::<Fq, U2>();
        test_halo2_insert_inner::<Fq, U4>();
        test_halo2_insert_inner::<Fq, U8>();
    }
}
