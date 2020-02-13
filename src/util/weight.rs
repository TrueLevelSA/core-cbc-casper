// Core CBC Casper
// Copyright (C) 2018 - 2020  Coordination Technology Ltd.
// Authors: pZ4 <pz4@protonmail.ch>,
//          Lederstrumpf,
//          h4sh3d <h4sh3d@truelevel.io>
//          roflolilolmao <q@truelevel.ch>
//
// This file is part of Core CBC Casper.
//
// Core CBC Casper is free software: you can redistribute it and/or modify it under the terms
// of the GNU Affero General Public License as published by the Free Software Foundation, either
// version 3 of the License, or (at your option) any later version.
//
// Core CBC Casper is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
// PURPOSE. See the GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License along with the Core CBC
// Rust Library. If not, see <https://www.gnu.org/licenses/>.

use std::cmp::Ordering;
use std::fmt::{self, Display};
use std::ops::{Add, AddAssign, Sub, SubAssign};

/// Defines how to compare the trait type to zero.
///
/// This trait is implemented for the basic types u8, u16, u32, u64, i8, i16, i32, and i64.
/// # Example
///
/// ```
/// use core_cbc_casper::util::weight::Zero;
///
/// #[derive(Copy, Clone, PartialEq)]
/// struct IntWrapper {
///     value: i32,
/// }
///
/// impl Zero<IntWrapper> for IntWrapper {
///     const ZERO: Self = Self { value: 0 };
/// }
///
/// assert!(IntWrapper::is_zero(&IntWrapper { value: 0 }));
/// ```
pub trait Zero<T: PartialEq + Copy> {
    const ZERO: T;

    /// Returns whether or not the value is equal to zero.
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}

macro_rules! impl_zero {
    ( $x:ty, $z:expr ) => {
        impl Zero<$x> for $x {
            const ZERO: Self = $z;

            fn is_zero(val: &Self) -> bool {
                *val == $z
            }
        }
    };
}

impl_zero!(u8, 0u8);
impl_zero!(u16, 0u16);
impl_zero!(u32, 0u32);
impl_zero!(u64, 0u64);
impl_zero!(i8, 0i8);
impl_zero!(i16, 0i16);
impl_zero!(i32, 0i32);
impl_zero!(i64, 0i64);

macro_rules! impl_weight_float {
    ( $x:ident, $z:expr ) => {
        impl Zero<$x> for $x {
            const ZERO: Self = $z;

            fn is_zero(val: &Self) -> bool {
                val > &-::std::$x::EPSILON && val < &::std::$x::EPSILON
            }
        }

        impl WeightUnit for $x {
            const NAN: Self = ::std::$x::NAN;
            const INFINITY: Self = ::std::$x::INFINITY;
        }
    };
}

impl_weight_float!(f32, 0f32);
impl_weight_float!(f64, 0f64);

/// Weight units for the validators.
///
/// # Example
///
/// The best example is the implementation of [`Weight`].
///
/// [`Weight`]: struct.Weight.html
pub trait WeightUnit
where
    Self: Zero<Self>
        + Add<Output = Self>
        + AddAssign
        + Sub<Output = Self>
        + SubAssign
        + Sized
        + PartialEq
        + PartialOrd
        + Copy,
{
    /// Represent not a number
    const NAN: Self;
    /// Points to infinity
    const INFINITY: Self;
}

/// Generic implementation of weight with any units that implement `std::ops::Add` and
/// `std::ops::Sub`. This type wraps the unit in a system with an infinity point and a
/// "not a number" point used by the algorithms.
///
/// Implements [`WeightUnit`] and [`Zero`].
///
/// [`WeightUnit`]: trait.WeightUnit.html
/// [`Zero`]: trait.Zero.html
///
/// # Example
///
/// ```
/// use core_cbc_casper::util::weight::Weight::{self, *};
///
/// assert_eq!(Unit(2), Unit(1) + Unit(1));
/// assert_eq!(Infinity, Unit(1) + Infinity);
/// assert_eq!(Weight::<u32>::NaN.to_string(), (Unit(1) + NaN).to_string());
/// ```
#[derive(Clone, Copy)]
pub enum Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    Unit(T),
    Infinity,
    NaN,
}

impl<T> Zero<Weight<T>> for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    const ZERO: Self = Weight::Unit(<T as Zero<T>>::ZERO);

    fn is_zero(val: &Self) -> bool {
        use Weight::*;

        match val {
            Unit(u) => *u == <T as Zero<T>>::ZERO,
            _ => false,
        }
    }
}

impl<T> PartialEq for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    fn eq(&self, other: &Self) -> bool {
        use Weight::*;

        match self {
            Unit(lhs) => match other {
                Unit(rhs) => lhs == rhs,
                _ => false,
            },
            Infinity => match other {
                // Inf equal Inf
                Infinity => true,
                // not equal to weight or NaN
                _ => false,
            },
            // NaN never equal to something
            NaN => false,
        }
    }
}

impl<T> PartialOrd for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Weight::*;

        match self {
            Unit(lhs) => match other {
                Unit(rhs) => lhs.partial_cmp(rhs),
                // number always smaller than infinity
                Infinity => Some(Ordering::Less),
                // NaN is not comparable
                NaN => None,
            },
            Infinity => match other {
                Unit(_) => Some(Ordering::Greater),
                // Inf is equal to Inf
                Infinity => Some(Ordering::Equal),
                // NaN is not comparable
                NaN => None,
            },
            // NaN is not comparable
            NaN => None,
        }
    }
}

impl<T> Add for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    type Output = Self;

    fn add(self, other: Self) -> Self {
        use Weight::*;

        match self {
            Unit(lhs) => match other {
                Unit(rhs) => Unit(lhs + rhs),
                Infinity => Infinity,
                NaN => NaN,
            },
            Infinity => match other {
                // NaN is always NaN
                NaN => NaN,
                // not NaN + Infinity is always Infinity
                _ => Infinity,
            },
            NaN => NaN,
        }
    }
}

impl<T> AddAssign for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

impl<T> Sub for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        use Weight::*;

        match self {
            Unit(lhs) => match other {
                Unit(rhs) => Unit(lhs - rhs),
                Infinity => Infinity,
                NaN => NaN,
            },
            Infinity => match other {
                // NaN is always NaN
                NaN => NaN,
                // Infinity - Infinity is not a number
                Infinity => NaN,
                // Infinity - x is still infinity
                Unit(_) => Infinity,
            },
            NaN => NaN,
        }
    }
}

impl<T> SubAssign for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}

impl<T> Display for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Weight::*;
        match self {
            Unit(int) => write!(f, "{}", int),
            Infinity => write!(f, "inf"),
            NaN => write!(f, "NaN"),
        }
    }
}

impl<T> fmt::Debug for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<T> WeightUnit for Weight<T>
where
    T: Zero<T> + Add<Output = T> + Sub<Output = T> + PartialEq + PartialOrd + Copy + Display,
{
    const NAN: Self = Weight::NaN;
    const INFINITY: Self = Weight::Infinity;
}

#[cfg(test)]
mod tests {
    use super::Weight::{self, *};

    // NaN is converted into string because NaN != NaN and then failed to pass
    // the tests.

    #[test]
    fn addition() {
        assert_eq!(Unit(2), Unit(1) + Unit(1));
        assert_eq!(Infinity, Unit(1) + Infinity);
        assert_eq!(Weight::<u32>::NaN.to_string(), (Unit(1) + NaN).to_string());
        assert_eq!(
            Weight::<u32>::NaN.to_string(),
            (Weight::<u32>::NaN + Weight::<u32>::NaN).to_string()
        );
        assert_eq!(Infinity, Infinity + Unit(1));
        assert_eq!(
            Weight::<u32>::NaN.to_string(),
            (Infinity + Weight::<u32>::NaN).to_string()
        );
        assert_eq!(Weight::<u32>::Infinity, Infinity + Infinity);
    }

    #[test]
    #[allow(clippy::eq_op)]
    fn substraction() {
        assert_eq!(Unit(0), Unit(1) - Unit(1));
        assert_eq!(Infinity, Unit(1) - Infinity);
        assert_eq!(Weight::<u32>::NaN.to_string(), (Unit(1) - NaN).to_string());
        assert_eq!(
            Weight::<u32>::NaN.to_string(),
            (Weight::<u32>::NaN - Weight::<u32>::NaN).to_string()
        );
        assert_eq!(Infinity, Infinity - Unit(1));
        assert_eq!(
            Weight::<u32>::NaN.to_string(),
            (Infinity - Weight::<u32>::NaN).to_string()
        );
        assert_eq!(
            Weight::<u32>::NaN.to_string(),
            (Infinity - Weight::<u32>::Infinity).to_string()
        );
    }

    #[test]
    #[allow(clippy::eq_op)]
    fn equality() {
        assert_eq!(true, Unit(1) == Unit(1));
        assert_eq!(false, Unit(1) == Infinity);
        assert_eq!(false, Unit(1) == NaN);
        assert_eq!(false, Weight::<u32>::NaN == Weight::<u32>::NaN);
        assert_eq!(false, Infinity == Weight::<u32>::NaN);
        assert_eq!(true, Infinity == Weight::<u32>::Infinity);
    }

    #[test]
    #[allow(clippy::eq_op)]
    fn greater() {
        assert_eq!(false, Unit(1) > Unit(1));
        assert_eq!(true, Unit(1) >= Unit(1));
        assert_eq!(false, Unit(1) > Weight::<u32>::Infinity);
        assert_eq!(false, Unit(1) >= Weight::<u32>::Infinity);
        assert_eq!(false, Unit(1) > Weight::<u32>::NaN);
        assert_eq!(false, Unit(1) >= Weight::<u32>::NaN);
        assert_eq!(false, Weight::<u32>::NaN > Weight::<u32>::NaN);
        assert_eq!(false, Weight::<u32>::NaN >= Weight::<u32>::NaN);
        assert_eq!(false, Weight::<u32>::Infinity > Weight::<u32>::NaN);
        assert_eq!(false, Weight::<u32>::Infinity >= Weight::<u32>::NaN);
        assert_eq!(true, Weight::<u32>::Infinity > Unit(1));
        assert_eq!(true, Weight::<u32>::Infinity >= Unit(1));
        assert_eq!(false, Weight::<u32>::Infinity > Weight::<u32>::Infinity);
        assert_eq!(true, Weight::<u32>::Infinity >= Weight::<u32>::Infinity);
    }

    #[test]
    #[allow(clippy::eq_op)]
    fn smaller() {
        assert_eq!(true, Unit(1) <= Unit(1));
        assert_eq!(false, Unit(1) < Unit(1));
        assert_eq!(true, Unit(1) <= Weight::<u32>::Infinity);
        assert_eq!(true, Unit(1) < Weight::<u32>::Infinity);
        assert_eq!(false, Unit(1) <= Weight::<u32>::NaN);
        assert_eq!(false, Unit(1) < Weight::<u32>::NaN);
        assert_eq!(false, Weight::<u32>::NaN <= Weight::<u32>::NaN);
        assert_eq!(false, Weight::<u32>::NaN < Weight::<u32>::NaN);
        assert_eq!(false, Weight::<u32>::NaN <= Weight::<u32>::Infinity);
        assert_eq!(false, Weight::<u32>::NaN < Weight::<u32>::Infinity);
        assert_eq!(false, Weight::<u32>::NaN <= Unit(1));
        assert_eq!(false, Weight::<u32>::NaN < Unit(1));
        assert_eq!(false, Weight::<u32>::Infinity <= Weight::<u32>::NaN);
        assert_eq!(false, Weight::<u32>::Infinity < Weight::<u32>::NaN);
        assert_eq!(true, Weight::<u32>::Infinity <= Weight::<u32>::Infinity);
        assert_eq!(false, Weight::<u32>::Infinity < Weight::<u32>::Infinity);
        assert_eq!(false, Weight::<u32>::Infinity <= Unit(1));
        assert_eq!(false, Weight::<u32>::Infinity < Unit(1));
    }
}
