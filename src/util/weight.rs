// Core CBC Rust Library
// Copyright (C) 2018  pZ4 <pz4@protonmail.ch>,
//                     Lederstrumpf,
//                     h4sh3d <h4sh3d@truelevel.io>
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

use std::ops::{Add, AddAssign, Mul, Sub, SubAssign};

/// Define how to compare the trait type to zero
pub trait Zero<T: PartialEq> {
    const ZERO: T;

    /// Returns whether or not the value is equal to zero.
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}

pub trait WeightUnit
where
    Self: Zero<Self>
        + Add<Output = Self>
        + AddAssign
        + Sub<Output = Self>
        + SubAssign
        + Mul<Output = Self>
        + Default
        + Sized
        + PartialEq
        + PartialOrd
        + Copy,
{
    const NAN: Self;
    const INFINITY: Self;
}

// Implement WeightUnit for f64
impl Zero<f64> for f64 {
    const ZERO: Self = 0.0f64;

    fn is_zero(val: &Self) -> bool {
        val > &-::std::f64::EPSILON && val < &::std::f64::EPSILON
    }
}

impl WeightUnit for f64 {
    const NAN: Self = ::std::f64::NAN;
    const INFINITY: Self = ::std::f64::INFINITY;
}
