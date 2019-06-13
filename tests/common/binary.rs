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

use casper::justification::LatestMsgsHonest;
use casper::message::{self, Trait};
#[cfg(feature = "integration_test")]
use casper::sender;
use casper::traits::Estimate;
use casper::util::weight::{SendersWeight, WeightUnit, Zero};

type Validator = u32;

#[derive(Clone, Eq, PartialEq, Debug, Hash, serde_derive::Serialize)]
pub struct BoolWrapper(pub bool);

#[cfg(feature = "integration_test")]
impl BoolWrapper {
    pub fn new(estimate: bool) -> Self {
        BoolWrapper(estimate)
    }
}

#[cfg(feature = "integration_test")]
impl<S: sender::Trait> From<S> for BoolWrapper {
    fn from(_sender: S) -> Self {
        BoolWrapper::new(bool::default())
    }
}

pub type BinaryMsg = message::Message<BoolWrapper /*Estimate*/, Validator /*Sender*/>;

impl Estimate for BoolWrapper {
    type M = BinaryMsg;

    /// weighted count of the votes contained in the latest messages
    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        senders_weights: &SendersWeight<<<Self as Estimate>::M as message::Trait>::Sender>,
        // _data: Option<<Self as Data>::Data>,
    ) -> Result<Self, &'static str> {
        // loop over all the latest messages
        let (true_w, false_w) = latest_msgs.iter().fold(
            (WeightUnit::ZERO, WeightUnit::ZERO),
            |(true_w, false_w), msg| {
                // get the weight for the sender
                let sender_weight = senders_weights
                    .weight(msg.sender())
                    .unwrap_or(WeightUnit::ZERO);

                // add the weight to the right accumulator
                if msg.estimate().0.clone() {
                    (true_w + sender_weight, false_w)
                } else {
                    (true_w, false_w + sender_weight)
                }
            },
        );

        Ok(BoolWrapper(true_w >= false_w))
    }
}
