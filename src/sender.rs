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

use std::fmt::Debug;
use std::hash::Hash;

/// All casper actors that send messages have to implement the sender trait
pub trait Trait: Hash + Clone + Ord + Eq + Send + Sync + Debug + serde::Serialize {}

// Default implementations
impl Trait for u8 {}
impl Trait for u32 {}
impl Trait for u64 {}
impl Trait for i8 {}
impl Trait for i32 {}
impl Trait for i64 {}
