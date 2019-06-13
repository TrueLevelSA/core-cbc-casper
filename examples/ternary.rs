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

extern crate casper;

use std::convert::From;

use casper::estimator::Estimate;
use casper::justification::LatestMsgsHonest;
use casper::message;
use casper::sender;

type Validator = u32;

pub type Message = message::Message<Value, Validator>;

#[derive(Debug, Hash, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, serde_derive::Serialize)]
pub enum Value {
    Zero = 0,
    One = 1,
    Two = 2,
}

impl From<((Value, f64), (Value, f64), (Value, f64))> for Value {
    /// If equality between two or tree values exists, last value is
    /// prefered, then second value, and first value
    ///
    /// v1: w1 > w2,  w1 > w3
    /// v2: w2 >= w1, w2 > w3
    /// v3: w3 >= w1, w3 >= w1
    ///
    fn from(val: ((Value, f64), (Value, f64), (Value, f64))) -> Self {
        let ((v1, w1), (v2, w2), (v3, w3)) = val;
        let mut max = v3;
        let mut w = w3;
        if w2 > w {
            max = v2;
            w = w2;
        }
        if w1 > w {
            max = v1;
        }
        max
    }
}

impl Estimate for Value {
    type M = Message;

    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Message>,
        senders_weights: &sender::Weights<Validator>,
    ) -> Result<Self, &'static str> {
        use message::Trait;
        let res: Self = latest_msgs
            .iter()
            .map(|msg| (msg.estimate(), senders_weights.weight(msg.sender())))
            .fold(
                ((Value::Zero, 0f64), (Value::One, 0f64), (Value::Two, 0f64)),
                |acc, t| match t {
                    (Value::Zero, Ok(weight)) => (((acc.0).0, (acc.0).1 + weight), acc.1, acc.2),
                    (Value::One, Ok(weight)) => (acc.0, ((acc.1).0, (acc.1).1 + weight), acc.2),
                    (Value::Two, Ok(weight)) => (acc.0, acc.1, ((acc.2).0, (acc.2).1 + weight)),
                    _ => acc, // No weight for the given validator, do nothing
                },
            )
            .into();
        Ok(res)
    }
}

fn main() {
    use std::collections::HashSet;

    use casper::justification::{Justification, LatestMsgs};
    use casper::message::Trait;

    let senders: Vec<u32> = (1..=4).collect();
    let weights = [0.6, 1.0, 2.0, 1.3];

    let senders_weights = sender::Weights::new(
        senders
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let weights = sender::State::new(
        senders_weights.clone(),
        0.0, // state fault weight
        None,
        LatestMsgs::empty(),
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    // 1: (1)  (2)
    // 2: (2)       (0)
    // 3: (0)  (0)       (0)
    // 4: (1)  (0)

    let msg1 = Message::new(1, Justification::empty(), Value::One);
    let msg2 = Message::new(2, Justification::empty(), Value::Two);
    let msg3 = Message::new(3, Justification::empty(), Value::Zero);
    let msg4 = Message::new(4, Justification::empty(), Value::One);
    let (msg5, _) = Message::from_msgs(1, vec![&msg1, &msg2], &weights).unwrap();
    let (msg6, _) = Message::from_msgs(3, vec![&msg3, &msg4], &weights).unwrap();
    let (msg7, _) = Message::from_msgs(2, vec![&msg2, &msg5, &msg6], &weights).unwrap();
    let (msg8, _) = Message::from_msgs(3, vec![&msg7, &msg6], &weights).unwrap();
    let (msg9, _) = Message::from_msgs(4, vec![&msg4, &msg6], &weights).unwrap();

    assert_eq!(msg5.estimate(), &Value::Two);
    assert_eq!(msg6.estimate(), &Value::Zero);
    assert_eq!(msg7.estimate(), &Value::Zero);
    assert_eq!(msg8.estimate(), &Value::Zero);
    assert_eq!(msg9.estimate(), &Value::Zero);
}
