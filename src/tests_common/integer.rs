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

use std::collections::HashSet;
use std::iter::FromIterator;

use crate::estimator::Estimator;
use crate::justification::LatestMsgsHonest;
use crate::message::Message;
use crate::util::weight::{WeightUnit, Zero};
use crate::validator;

type Validator = u32;

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash, serde_derive::Serialize)]
pub struct IntegerWrapper(pub u32);

#[cfg(feature = "integration_test")]
impl IntegerWrapper {
    pub fn new(estimate: u32) -> Self {
        IntegerWrapper(estimate)
    }
}

#[cfg(feature = "integration_test")]
impl<V: validator::ValidatorName> From<V> for IntegerWrapper {
    fn from(_validator: V) -> Self {
        IntegerWrapper::new(u32::default())
    }
}

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash)]
pub struct Tx;

#[derive(Debug, PartialEq)]
pub struct Error(&'static str);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "{}", self.0)
    }
}

impl std::error::Error for Error {}

impl std::convert::From<&'static str> for Error {
    fn from(e: &'static str) -> Self {
        Error(e)
    }
}

/// the goal here is to find the weighted median of all the values
impl Estimator for IntegerWrapper {
    type ValidatorName = Validator;
    type Error = Error;

    fn estimate<U: WeightUnit>(
        latest_msgs: &LatestMsgsHonest<Self>,
        validators_weights: &validator::Weights<Validator, U>,
    ) -> Result<Self, Self::Error> {
        let mut msgs_sorted_by_estimate = Vec::from_iter(latest_msgs.iter().fold(
            HashSet::new(),
            |mut latest, latest_from_validator| {
                latest.insert(latest_from_validator);
                latest
            },
        ));
        msgs_sorted_by_estimate.sort_unstable_by(|a, b| a.estimate().cmp(&b.estimate()));

        // get the total weight of the validators of the messages
        // in the set
        let total_weight = msgs_sorted_by_estimate
            .iter()
            .fold(<U as Zero<U>>::ZERO, |acc, x| {
                acc + validators_weights.weight(x.sender()).unwrap_or(U::NAN)
            });

        let mut running_weight = <U as Zero<U>>::ZERO;
        let mut msg_iter = msgs_sorted_by_estimate.iter();
        let mut current_msg: Result<&&Message<IntegerWrapper>, &str> = Err("no msg");

        // since the messages are ordered according to their estimates,
        // whichever estimate is found after iterating over half of the total weight
        // is the consensus
        while running_weight + running_weight < total_weight {
            current_msg = msg_iter.next().ok_or("no next msg");
            running_weight += current_msg
                .and_then(|m| {
                    validators_weights
                        .weight(m.sender())
                        .map_err(|_| "Can't unwrap weight")
                })
                .unwrap_or(U::NAN)
        }

        // return said estimate
        current_msg
            .map(|m| m.estimate().clone())
            .map_err(From::from)
    }
}
