// Core CBC Rust Library
// Copyright (C) 2018  Coordination Technology Ltd.
// Authors: pZ4 <pz4@protonmail.ch>,
//          Lederstrumpf,
//          h4sh3d <h4sh3d@truelevel.io>
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

#[cfg(test)]
macro_rules! float_eq {
    ($lhs:expr, $rhs:expr) => {{
        assert!(
            f32::abs($lhs - $rhs) < std::f32::EPSILON,
            format!("float_eq: {} and {} aren't equal", $lhs, $rhs),
        )
    }};
    ($lhs:expr, $rhs:expr, $message:expr) => {{
        assert!(
            f32::abs($lhs - $rhs) < std::f32::EPSILON,
            format!(
                "float_eq: {} and {} aren't equal. Provided message: {}",
                $lhs, $rhs, $message
            ),
        )
    }};
}
