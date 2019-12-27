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

use crate::blockchain::BlockData;
use crate::validator::ValidatorName;

/// This block data structure contains the name of the validator that created that block. This is
/// used by the tests in order to have a simple data structure.
#[derive(std::hash::Hash, Clone, Eq, PartialEq, Default)]
pub struct ValidatorNameBlockData<V: ValidatorName + Default> {
    validator_name: V,
}

impl<V: ValidatorName + Default> ValidatorNameBlockData<V> {
    pub fn new(validator_name: V) -> Self {
        ValidatorNameBlockData { validator_name }
    }
}

impl<V: ValidatorName + Default> BlockData for ValidatorNameBlockData<V> {
    type ValidatorName = V;

    fn validator_name(&self) -> &Self::ValidatorName {
        &self.validator_name
    }
}

impl<V: ValidatorName + Default> serde::Serialize for ValidatorNameBlockData<V> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        let mut s = serializer.serialize_struct("ValidatorNameBlockData", 1)?;
        s.serialize_field("validator_name", &self.validator_name)?;
        s.end()
    }
}
