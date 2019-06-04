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

extern crate digest;
#[cfg(feature = "integration_test")]
extern crate proptest;
#[cfg(feature = "integration_test")]
extern crate rand;
extern crate rayon;

extern crate bincode;
extern crate blake2;
extern crate itertools;
extern crate serde;
extern crate serde_derive;

pub mod blockchain;
pub mod justification;
pub mod message;
pub mod traits;
pub mod util;
