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

use casper::estimator::Estimate;
use casper::justification::LatestMsgsHonest;
use casper::message::{self, Trait};
use casper::sender;
use casper::util::weight::{WeightUnit, Zero};

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
impl<S: sender::Trait> From<S> for IntegerWrapper {
    fn from(_sender: S) -> Self {
        IntegerWrapper::new(u32::default())
    }
}

pub type IntegerMsg = message::Message<IntegerWrapper /*Estimate*/, Validator /*Sender*/>;

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash)]
pub struct Tx;

/// the goal here is to find the weighted median of all the values
impl Estimate for IntegerWrapper {
    type M = IntegerMsg;

    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        senders_weights: &sender::Weights<<<Self as Estimate>::M as message::Trait>::Sender>,
    ) -> Result<Self, &'static str> {
        let mut msgs_sorted_by_estimate = Vec::from_iter(latest_msgs.iter().fold(
            HashSet::new(),
            |mut latest, latest_from_validator| {
                latest.insert(latest_from_validator);
                latest
            },
        ));
        msgs_sorted_by_estimate.sort_unstable_by(|a, b| a.estimate().cmp(&b.estimate()));

        // get the total weight of the senders of the messages
        // in the set
        let total_weight = msgs_sorted_by_estimate
            .iter()
            .fold(WeightUnit::ZERO, |acc, x| {
                acc + senders_weights
                    .weight(x.sender())
                    .unwrap_or(WeightUnit::ZERO)
            });

        let mut running_weight = 0.0;
        let mut msg_iter = msgs_sorted_by_estimate.iter();
        let mut current_msg: Result<&&IntegerMsg, &str> = Err("no msg");

        // since the messages are ordered according to their estimates,
        // whichever estimate is found after iterating over half of the total weight
        // is the consensus
        while running_weight / total_weight < 0.5 {
            current_msg = msg_iter.next().ok_or("no next msg");
            running_weight += current_msg
                .and_then(|m| senders_weights.weight(m.sender()))
                .unwrap_or(WeightUnit::ZERO)
        }

        // return said estimate
        current_msg.map(|m| m.estimate().clone())
    }
}
