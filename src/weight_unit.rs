use traits::{Zero};

pub type WeightUnit = f64;

impl Zero<WeightUnit> for WeightUnit {
    const ZERO: Self = 0.0f64;

    fn is_zero(val: &Self) -> bool {
        val > &-::std::f64::EPSILON && val < &::std::f64::EPSILON
    }
}
