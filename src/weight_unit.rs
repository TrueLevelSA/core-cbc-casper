use std::{f64};
use zero::{Zero};
pub type WeightUnit = f64;

impl Zero<WeightUnit> for WeightUnit {
    const ZERO: Self = 0.0f64;
    fn is_zero(val: &Self) -> bool {
        val > &-f64::EPSILON && val < &f64::EPSILON
    }
}
