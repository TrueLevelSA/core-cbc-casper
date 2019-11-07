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

use std::error::Error;
use std::fmt::Debug;
use std::hash::Hash;

use crate::justification::LatestMsgsHonest;
use crate::util::weight::WeightUnit;
use crate::validator;

/// Describes an estimate, or a value of the consensus at a certain time. Implementing this trait
/// allows to produce an estimate given the set of latest messages and the set of validators and
/// their weights.
pub trait Estimator: Hash + Eq + Clone + Send + Sync + Debug + serde::Serialize {
    type ValidatorName: validator::ValidatorName;
    type Error: Error;

    /// Choses an estimate from a set of latest messages.
    fn estimate<U: WeightUnit>(
        latest_msgs: &LatestMsgsHonest<Self>,
        validators_weights: &validator::Weights<Self::ValidatorName, U>,
    ) -> Result<Self, Self::Error>;
}
