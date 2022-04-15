use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::AssignedCell,
    plonk::{Assigned, Expression},
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
