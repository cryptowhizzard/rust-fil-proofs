use std::marker::PhantomData;

use filecoin_hashers::{Domain, HaloHasher, PoseidonArity};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter},
    plonk::{self, ConstraintSystem},
};

use crate::{
    gadgets::halo2::{AssignedBit, InsertChip, InsertConfig},
};

#[derive(Clone)]
pub struct MerkleConfig<H, U, V, W>
where
    H: HaloHasher,
    <H::Domain as Domain>::Field: FieldExt,
    U: PoseidonArity<<H::Domain as Domain>::Field>,
    V: PoseidonArity<<H::Domain as Domain>::Field>,
    W: PoseidonArity<<H::Domain as Domain>::Field>,
{
    base_hasher: H::Config,
    base_insert: InsertConfig,
    sub: Option<(H::Config, InsertConfig)>,
    top: Option<(H::Config, InsertConfig)>,
    _u: PhantomData<U>,
    _v: PhantomData<V>,
    _w: PhantomData<W>,
}

pub struct MerkleChip<H, U, V, W>
where
    H: HaloHasher,
    <H::Domain as Domain>::Field: FieldExt,
    U: PoseidonArity<<H::Domain as Domain>::Field>,
    V: PoseidonArity<<H::Domain as Domain>::Field>,
    W: PoseidonArity<<H::Domain as Domain>::Field>,
{
    config: MerkleConfig<H, U, V, W>,
}

impl<H, U, V, W> MerkleChip<H, U, V, W>
where
    H: HaloHasher,
    <H::Domain as Domain>::Field: FieldExt,
    U: PoseidonArity<<H::Domain as Domain>::Field>,
    V: PoseidonArity<<H::Domain as Domain>::Field>,
    W: PoseidonArity<<H::Domain as Domain>::Field>,
{
    pub fn construct(config: MerkleConfig<H, U, V, W>) -> Self {
        MerkleChip { config }
    }

    pub fn configure(
        _meta: &mut ConstraintSystem<<H::Domain as Domain>::Field>,
        base_hasher: H::Config,
        base_insert: InsertConfig,
        sub: Option<(H::Config, InsertConfig)>,
        top: Option<(H::Config, InsertConfig)>,
    ) -> MerkleConfig<H, U, V, W> {
        if V::to_usize() == 0 {
            assert!(sub.is_none());
        }
        if W::to_usize() == 0 {
            assert!(top.is_none());
        }
        MerkleConfig {
            base_hasher,
            base_insert,
            sub,
            top,
            _u: PhantomData,
            _v: PhantomData,
            _w: PhantomData,
        }
    }

    #[allow(unused_assignments)]
    pub fn compute_root(
        &self,
        mut layouter: impl Layouter<<H::Domain as Domain>::Field>,
        challenge_bits: &[AssignedBit<<H::Domain as Domain>::Field>],
        leaf: &Option<<H::Domain as Domain>::Field>,
        path: &[Vec<Option<<H::Domain as Domain>::Field>>],
    ) -> Result<
        AssignedCell<<H::Domain as Domain>::Field, <H::Domain as Domain>::Field>,
        plonk::Error,
    > {
        let base_arity = U::to_usize();
        let sub_arity = V::to_usize();
        let top_arity = W::to_usize();

        let base_arity_bit_len = base_arity.trailing_zeros();
        let sub_arity_bit_len = sub_arity.trailing_zeros();
        let top_arity_bit_len = top_arity.trailing_zeros();

        let base_path_len = if top_arity > 0 {
            path.len() - 2
        } else if sub_arity > 0 {
            path.len() - 1
        } else {
            path.len()
        };

        let mut cur = None;
        let mut height = 0;
        let mut path_values = path.into_iter();
        let mut challenge_bits = challenge_bits.into_iter();

        let base_insert_chip = InsertChip::<<H::Domain as Domain>::Field, U>::construct(
            self.config.base_insert.clone(),
        );

        for _ in 0..base_path_len {
            let siblings = path_values.next().expect("no path elements remaining");

            assert_eq!(
                siblings.len(),
                base_arity - 1,
                "path element has incorrect number of siblings"
            );

            let index_bits: Vec<AssignedBit<<H::Domain as Domain>::Field>> = (0..base_arity_bit_len)
                .map(|_| challenge_bits.next().expect("no challenge bits remaining").clone())
                .collect();

            let preimage = if height == 0 {
                base_insert_chip.assign_value_then_insert(
                    layouter.namespace(|| format!("insert (height {})", height)),
                    &siblings,
                    leaf,
                    &index_bits,
                )?
            } else {
                base_insert_chip.insert(
                    layouter.namespace(|| format!("insert (height {})", height)),
                    &siblings,
                    &cur.take().unwrap(),
                    &index_bits,
                )?
            };

            let digest = H::hash_circuit_packed(
                layouter.namespace(|| format!("merkle hash (height {})", height)),
                // TODO: figure out a way to not clone the config on each hash function.
                self.config.base_hasher.clone(),
                &preimage,
            )?;

            cur = Some(digest);
            height += 1;
        }

        if sub_arity > 0 {
            let siblings = path_values.next().expect("no path elements remaining");

            assert_eq!(
                siblings.len(),
                sub_arity - 1,
                "path element has incorrect number of siblings"
            );

            let index_bits: Vec<AssignedBit<<H::Domain as Domain>::Field>> = (0..sub_arity_bit_len)
                .map(|_| challenge_bits.next().expect("no challenge bits remaining").clone())
                .collect();

            let (hasher_config, insert_config) = self.config.sub.clone().unwrap();

            let sub_insert_chip =
                InsertChip::<<H::Domain as Domain>::Field, V>::construct(insert_config);

            let preimage = sub_insert_chip.insert(
                layouter.namespace(|| format!("insert (height {})", height)),
                &siblings,
                &cur.take().unwrap(),
                &index_bits,
            )?;

            let digest = H::hash_circuit_packed(
                layouter.namespace(|| format!("merkle hash (height {})", height)),
                hasher_config,
                &preimage,
            )?;

            cur = Some(digest);
            height += 1;
        }

        if top_arity > 0 {
            let siblings = path_values.next().expect("no path elements remaining");

            assert_eq!(
                siblings.len(),
                top_arity - 1,
                "path element has incorrect number of siblings"
            );

            let index_bits: Vec<AssignedBit<<H::Domain as Domain>::Field>> = (0..top_arity_bit_len)
                .map(|_| challenge_bits.next().expect("no challenge bits remaining").clone())
                .collect();

            let (hasher_config, insert_config) = self.config.top.clone().unwrap();

            let top_insert_chip =
                InsertChip::<<H::Domain as Domain>::Field, W>::construct(insert_config);

            let preimage = top_insert_chip.insert(
                layouter.namespace(|| format!("insert (height {})", height)),
                &siblings,
                &cur.take().unwrap(),
                &index_bits,
            )?;

            let digest = H::hash_circuit_packed(
                layouter.namespace(|| format!("merkle hash (height {})", height)),
                hasher_config,
                &preimage,
            )?;

            cur = Some(digest);
            height += 1;
        }

        Ok(cur.unwrap())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::cmp::max;
    use std::iter;

    use ff::PrimeField;
    use filecoin_hashers::{poseidon::PoseidonHasher, HashFunction};
    use generic_array::typenum::{U0, U2, U4, U8};
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        pasta::Fp,
        plonk::{Advice, Circuit, Column, Fixed},
    };
    use merkletree::store::VecStore;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use crate::{
        gadgets::halo2::{Bit, InsertChip},
        merkle::{generate_tree, MerkleProofTrait, MerkleTreeTrait, MerkleTreeWrapper},
        TEST_SEED,
    };

    #[derive(Clone)]
    struct MyConfig<H, U, V, W>
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        merkle: MerkleConfig<H, U, V, W>,
        advice_eq: Vec<Column<Advice>>,
    }

    struct MyCircuit<H, U, V, W, const CHALLENGE_BIT_LEN: usize>
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        challenge_bits: Vec<Option<bool>>,
        leaf: Option<<H::Domain as Domain>::Field>,
        path: Vec<Vec<Option<<H::Domain as Domain>::Field>>>,
        _u: PhantomData<U>,
        _v: PhantomData<V>,
        _w: PhantomData<W>,
    }

    impl<H, U, V, W, const CHALLENGE_BIT_LEN: usize> Circuit<<H::Domain as Domain>::Field> for
        MyCircuit<H, U, V, W, CHALLENGE_BIT_LEN>
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        type Config = MyConfig<H, U, V, W>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            let base_arity = U::to_usize();
            let sub_arity = V::to_usize();
            let top_arity = W::to_usize();

            let base_arity_bit_len = base_arity.trailing_zeros() as usize;
            let sub_arity_bit_len = sub_arity.trailing_zeros() as usize;
            let top_arity_bit_len = top_arity.trailing_zeros() as usize;

            let challenge_bits = vec![None; CHALLENGE_BIT_LEN];

            let path = if top_arity > 0 {
                let base_challenge_bit_len =
                    CHALLENGE_BIT_LEN - (sub_arity_bit_len + top_arity_bit_len);
                let base_path_len = base_challenge_bit_len / base_arity_bit_len;
                iter::repeat(base_arity)
                    .take(base_path_len)
                    .chain(iter::once(sub_arity))
                    .chain(iter::once(top_arity))
                    .map(|arity| vec![None; arity - 1])
                    .collect()
            } else if sub_arity > 0 {
                let base_challenge_bit_len = CHALLENGE_BIT_LEN - sub_arity_bit_len;
                let base_path_len = base_challenge_bit_len / base_arity_bit_len;
                iter::repeat(base_arity)
                    .take(base_path_len)
                    .chain(iter::once(sub_arity))
                    .map(|arity| vec![None; arity - 1])
                    .collect()
            } else {
                let base_path_len = CHALLENGE_BIT_LEN / base_arity_bit_len;
                vec![vec![None; base_arity - 1]; base_path_len]
            };

            MyCircuit {
                challenge_bits,
                leaf: None,
                path: path,
                _u: PhantomData,
                _v: PhantomData,
                _w: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<<H::Domain as Domain>::Field>) -> Self::Config {
            let hasher_spec = H::column_spec::<U>();
            let base_insert_spec = InsertChip::<<H::Domain as Domain>::Field, U>::column_spec();
            let sub_insert_spec = InsertChip::<<H::Domain as Domain>::Field, V>::column_spec();
            let top_insert_spec = InsertChip::<<H::Domain as Domain>::Field, W>::column_spec();

            let num_advice_eq = max(
                max(hasher_spec.advice_eq, base_insert_spec.advice_eq),
                CHALLENGE_BIT_LEN,
            );
            let num_advice_neq = max(hasher_spec.advice_neq, base_insert_spec.advice_neq);
            let num_fixed_eq = max(hasher_spec.fixed_eq, base_insert_spec.fixed_eq);
            let num_fixed_neq = max(hasher_spec.fixed_neq, base_insert_spec.fixed_neq);

            let advice_eq: Vec<Column<Advice>> =
                (0..num_advice_eq).map(|_| meta.advice_column()).collect();
            let advice_neq: Vec<Column<Advice>> =
                (0..num_advice_neq).map(|_| meta.advice_column()).collect();
            let fixed_eq: Vec<Column<Fixed>> =
                (0..num_fixed_eq).map(|_| meta.fixed_column()).collect();
            let fixed_neq: Vec<Column<Fixed>> =
                (0..num_fixed_neq).map(|_| meta.fixed_column()).collect();

            for col in advice_eq.iter() {
                meta.enable_equality(*col);
            }
            for col in fixed_eq.iter() {
                meta.enable_equality(*col);
            }

            let base_hasher =
                H::configure::<U>(meta, &advice_eq, &advice_neq, &fixed_eq, &fixed_neq);

            let base_insert = InsertChip::<<H::Domain as Domain>::Field, U>::configure(
                meta,
                &advice_eq[..base_insert_spec.advice_eq],
                &advice_neq[..base_insert_spec.advice_neq],
            );

            let sub = if V::to_usize() == 0 {
                None
            } else {
                let sub_hasher = 
                    H::configure::<V>(meta, &advice_eq, &advice_neq, &fixed_eq, &fixed_neq);
                let sub_insert = InsertChip::<<H::Domain as Domain>::Field, V>::configure(
                    meta,
                    &advice_eq[..sub_insert_spec.advice_eq],
                    &advice_neq[..sub_insert_spec.advice_neq],
                );
                Some((sub_hasher, sub_insert))
            };

            let top = if W::to_usize() == 0 {
                None
            } else {
                let top_hasher = 
                    H::configure::<W>(meta, &advice_eq, &advice_neq, &fixed_eq, &fixed_neq);
                let top_insert = InsertChip::<<H::Domain as Domain>::Field, W>::configure(
                    meta,
                    &advice_eq[..top_insert_spec.advice_eq],
                    &advice_neq[..top_insert_spec.advice_neq],
                );
                Some((top_hasher, top_insert))
            };

            let merkle = MerkleChip::configure(meta, base_hasher, base_insert, sub, top);

            MyConfig {
                merkle,
                advice_eq,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<<H::Domain as Domain>::Field>,
        ) -> Result<(), plonk::Error> {
            let chip = MerkleChip::construct(config.merkle.clone());

            // Allocate the challenge bits.
            let challenge_bits: Vec<AssignedBit<<H::Domain as Domain>::Field>> = layouter.assign_region(
                || "challenge_bits",
                |mut region| {
                    let row = 0;
                    self.challenge_bits
                        .iter()
                        .enumerate()
                        .map(|(i, opt)| {
                            region.assign_advice(
                                || format!("challenge bit {}", i),
                                config.advice_eq[i],
                                row,
                                || opt.map(Bit).ok_or(plonk::Error::Synthesis),
                            )
                        })
                        .collect()
                },
            )?;

            // Compute the root from the provided Merkle path.
            let root = chip.compute_root(layouter, &challenge_bits, &self.leaf, &self.path)?;

            let expected_root = expected_root::<H>(&self.challenge_bits, &self.leaf, &self.path);
            assert_eq!(root.value(), Some(&expected_root));

            Ok(())
        }
    }

    impl<H, U, V, W, const CHALLENGE_BIT_LEN: usize> MyCircuit<H, U, V, W, CHALLENGE_BIT_LEN>
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        fn with_witness(
            challenge_bits: Vec<bool>,
            leaf: <H::Domain as Domain>::Field,
            path: Vec<Vec<<H::Domain as Domain>::Field>>,
        ) -> Self {
            MyCircuit {
                challenge_bits: challenge_bits.into_iter().map(Some).collect(),
                leaf: Some(leaf),
                path: path.into_iter().map(|siblings| siblings.into_iter().map(Some).collect()).collect(),
                _u: PhantomData,
                _v: PhantomData,
                _w: PhantomData,
            }
        }

        fn k() -> u32 {
            let base_arity = U::to_usize();
            let sub_arity = V::to_usize();
            let top_arity = W::to_usize();

            let base_arity_bit_len = base_arity.trailing_zeros() as usize;
            let sub_arity_bit_len = sub_arity.trailing_zeros() as usize;
            let top_arity_bit_len = top_arity.trailing_zeros() as usize;

            let mut base_challenge_bit_len = CHALLENGE_BIT_LEN;
            if sub_arity > 0 {
                base_challenge_bit_len -= sub_arity_bit_len;
            }
            if top_arity > 0 {
                base_challenge_bit_len -= top_arity_bit_len;
            }
            let base_path_len = base_challenge_bit_len / base_arity_bit_len;

            let base_hasher_rows = match base_arity {
                0 => 0,
                2 | 4 => 36,
                8 => 37,
                _ => unimplemented!(),
            };
            let sub_hasher_rows = match sub_arity {
                0 => 0,
                2 | 4 => 36,
                8 => 37,
                _ => unimplemented!(),
            };
            let top_hasher_rows = match top_arity {
                0 => 0,
                2 | 4 => 36,
                8 => 37,
                _ => unimplemented!(),
            };
            let insert_rows = 1;

            // One row for initial value allocations.
            let mut num_rows = 1;
            num_rows += base_path_len * (base_hasher_rows + insert_rows);
            if sub_arity > 0 {
                num_rows += sub_hasher_rows + insert_rows;
            }
            if top_arity > 0 {
                num_rows += top_hasher_rows + insert_rows;
            };

            (num_rows as f32).log2().ceil() as u32
        }
    }

    fn expected_root<H>(
        challenge_bits: &[Option<bool>],
        leaf: &Option<<H::Domain as Domain>::Field>,
        path: &[Vec<Option<<H::Domain as Domain>::Field>>],
    ) -> <H::Domain as Domain>::Field
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
    {
        let mut cur = leaf.clone().unwrap();
        let mut challenge_bits = challenge_bits.iter().map(|opt| opt.unwrap());

        for siblings in path.iter() {
            let arity = siblings.len() + 1;
            let index_bit_len = arity.trailing_zeros() as usize;

            let index = (0..index_bit_len).fold(0, |acc, i| {
                let bit = challenge_bits.next().unwrap() as usize;
                acc + (bit << i)
            });

            let mut preimage = Vec::<u8>::with_capacity(arity << 5);
            for sib in &siblings[..index] {
                preimage.extend_from_slice(sib.clone().unwrap().to_repr().as_ref())
            }
            preimage.extend_from_slice(cur.to_repr().as_ref());
            for sib in &siblings[index..] {
                preimage.extend_from_slice(sib.clone().unwrap().to_repr().as_ref())
            }

            cur = H::Function::hash(&preimage).into();
        }

        cur
    }

    fn test_halo2_merkle_chip_inner<H, U, V, W, const CHALLENGE_BIT_LEN: usize>()
    where
        H: 'static + HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        let num_leafs = 1 << CHALLENGE_BIT_LEN;

        let mut rng = XorShiftRng::from_seed(TEST_SEED);
        let (_, tree) = generate_tree::<MerkleTreeWrapper<H, VecStore<H::Domain>, U, V, W>, _>(
            &mut rng,
            num_leafs,
            None,
        );

        for challenge in 0..num_leafs {
            let merkle_proof = tree.gen_proof(challenge).unwrap();

            let challenge_bits =
                (0..CHALLENGE_BIT_LEN).map(|i| (challenge >> i) & 1 == 1).collect();

            let leaf = merkle_proof.leaf().into();

            let path = merkle_proof
                .path()
                .into_iter()
                .map(|(siblings, _index)| siblings.into_iter().map(Into::into).collect())
                .collect();

            let circ = MyCircuit::<H, U, V, W, CHALLENGE_BIT_LEN>::with_witness(
                challenge_bits,
                leaf,
                path,
            );

            let k = MyCircuit::<H, U, V, W, CHALLENGE_BIT_LEN>::k();
            let prover = MockProver::run(k, &circ, vec![]).unwrap();
            assert!(prover.verify().is_ok());
        }
    }

    #[test]
    fn test_halo2_merkle_chip() {
        // All inner tests are using the same base tree height, therefore the challenge bit length
        // is `base_height * log2(base_arity) + log2(sub_arity) + log2(top_arity)`.
        const BASE_HEIGHT: usize = 2;

        // Arity 2
        {
            const CHALLENGE_BIT_LEN: usize = BASE_HEIGHT * 1;
            test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U2, U0, U0, CHALLENGE_BIT_LEN>();
        }

        // Arity 4
        {
            const CHALLENGE_BIT_LEN: usize = BASE_HEIGHT * 2;
            test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U4, U0, U0, CHALLENGE_BIT_LEN>();
        }

        // Arity 8
        {
            const CHALLENGE_BIT_LEN: usize = BASE_HEIGHT * 3;
            test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U8, U0, U0, CHALLENGE_BIT_LEN>();
            test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U8, U8, U0, CHALLENGE_BIT_LEN>();
        }

        // Arity 8-2
        {
            const CHALLENGE_BIT_LEN: usize = BASE_HEIGHT * 3 + 1;
            test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U8, U2, U0, CHALLENGE_BIT_LEN>();
            test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U8, U8, U2, CHALLENGE_BIT_LEN>();
        }

        // Arity 8-4
        {
            const CHALLENGE_BIT_LEN: usize = BASE_HEIGHT * 3 + 2;
            test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U8, U4, U0, CHALLENGE_BIT_LEN>();
            test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U8, U8, U4, CHALLENGE_BIT_LEN>();
        }

        // Arity 8-4-2
        {
            const CHALLENGE_BIT_LEN: usize = BASE_HEIGHT * 3 + 2 + 1;
            test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U8, U4, U2, CHALLENGE_BIT_LEN>();
        }
    }
}
