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

#[macro_use]
extern crate criterion;

use core_cbc_casper::estimator::Estimator;
use core_cbc_casper::justification::LatestMessagesHonest;
use core_cbc_casper::message;
use core_cbc_casper::util::weight::{WeightUnit, Zero};
use core_cbc_casper::validator;
use core_cbc_casper::Block;
use core_cbc_casper::ValidatorNameBlockData;
use criterion::{black_box, Criterion};

type Validator = u8;

#[derive(Debug, Hash, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, serde_derive::Serialize)]
pub enum Value {
    Zero = 0,
    One = 1,
    Two = 2,
}

impl validator::ValidatorName for Value {}

impl<U: WeightUnit> From<((Value, U), (Value, U), (Value, U))> for Value {
    /// If equality between two or tree values exists, last value is
    /// prefered, then second value, and first value
    ///
    /// v1: w1 > w2,  w1 > w3
    /// v2: w2 >= w1, w2 > w3
    /// v3: w3 >= w1, w3 >= w1
    ///
    fn from(val: ((Value, U), (Value, U), (Value, U))) -> Self {
        let ((v1, w1), (v2, w2), (v3, w3)) = val;
        let mut max = v3;
        let mut weight = w3;
        if w2 > weight {
            max = v2;
            weight = w2;
        }
        if w1 > weight {
            max = v1;
        }
        max
    }
}

#[derive(Debug)]
pub struct Error(&'static str);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "{}", self.0)
    }
}

impl std::error::Error for Error {}

impl std::convert::From<&'static str> for Error {
    fn from(string: &'static str) -> Self {
        Error(string)
    }
}

impl Estimator for Value {
    type ValidatorName = Validator;
    type Error = Error;

    fn estimate<U: WeightUnit>(
        latest_messages: &LatestMessagesHonest<Self>,
        validators_weights: &validator::Weights<Validator, U>,
    ) -> Result<Self, Self::Error> {
        let res: Self = latest_messages
            .iter()
            .map(|message| {
                (
                    message.estimate(),
                    validators_weights.weight(message.sender()),
                )
            })
            .fold(
                (
                    (Value::Zero, <U as Zero<U>>::ZERO),
                    (Value::One, <U as Zero<U>>::ZERO),
                    (Value::Two, <U as Zero<U>>::ZERO),
                ),
                |acc, tuple| match tuple {
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

fn block_new(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "Block::new",
        |b, loops| {
            b.iter(|| {
                let mut block = None;
                for _ in 0..(**loops) {
                    block = Some(Block::new(block, ValidatorNameBlockData::new(0)));
                }
            });
        },
        &[1_000, 10 * 1_000, 100 * 1_000],
    );
}

fn block_from_prevblock_message(c: &mut Criterion) {
    type Message = message::Message<Value>;

    c.bench_function_over_inputs(
        "Block::from_prevblock_message",
        |b, loops| {
            use std::collections::HashSet;

            use core_cbc_casper::justification::{Justification, LatestMessages};

            let validators: Vec<u8> = (1..=4).collect();
            let weights = [0.6, 1.0, 2.0, 1.3];

            let validators_weights = validator::Weights::new(
                validators
                    .iter()
                    .cloned()
                    .zip(weights.iter().cloned())
                    .collect(),
            );

            let mut weights = validator::State::new(
                validators_weights,
                0.0,
                LatestMessages::empty(),
                1.0,
                HashSet::new(),
            );
            let block = Block::new(None, ValidatorNameBlockData::new(0));
            let mut message = Message::new(1, Justification::empty(), Value::One);
            for _ in 0..=(**loops) {
                weights.update(&[&message]);
                message = Message::from_validator_state(1, &weights).unwrap();
            }

            b.iter(|| {
                Block::from_prevblock_message(black_box(None), black_box(block.clone()));
            });
        },
        &[100, 1_000, 10_000],
    );
}

fn block_is_member(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "Block::is_member",
        |b, loops| {
            let first_block = Block::new(None, ValidatorNameBlockData::new(0));
            let mut block = Block::new(Some(first_block.clone()), ValidatorNameBlockData::new(0));
            for _ in 0..(**loops) {
                block = Block::new(Some(block), ValidatorNameBlockData::new(0));
            }
            b.iter(|| first_block.is_member(&block));
        },
        &[10, 100, 1_000],
    );
}

fn block_estimate(c: &mut Criterion) {
    use core_cbc_casper::justification::{Justification, LatestMessages};
    use core_cbc_casper::message::Message;
    use std::collections::HashSet;

    let weights = validator::Weights::new(
        vec![(0, 1.0), (1, 2.0), (2, 4.0), (3, 8.0), (4, 16.0)]
            .into_iter()
            .collect(),
    );
    let genesis = Block::new(None, ValidatorNameBlockData::new(0));
    let block_1 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(1));
    let block_2 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(2));
    let block_3 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(3));
    let block_4 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(4));

    let block_5 = Block::new(Some(block_4.clone()), ValidatorNameBlockData::new(0));
    let block_6 = Block::new(Some(block_2.clone()), ValidatorNameBlockData::new(3));

    let block_7 = Block::new(Some(block_5.clone()), ValidatorNameBlockData::new(2));
    let block_8 = Block::new(Some(block_6.clone()), ValidatorNameBlockData::new(4));

    let mut justification = Justification::empty();
    justification.insert(Message::new(0, justification.clone(), genesis));
    justification.insert(Message::new(1, justification.clone(), block_1));
    justification.insert(Message::new(2, justification.clone(), block_2));
    justification.insert(Message::new(3, justification.clone(), block_3));
    justification.insert(Message::new(4, justification.clone(), block_4));
    justification.insert(Message::new(0, justification.clone(), block_5));
    justification.insert(Message::new(3, justification.clone(), block_6));
    justification.insert(Message::new(2, justification.clone(), block_7));
    justification.insert(Message::new(4, justification.clone(), block_8));
    let latest_messages = LatestMessages::from(&justification);
    let latest_honest_messages =
        LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new());

    c.bench_function("Block::estimate", move |b| {
        b.iter(|| Block::estimate(black_box(&latest_honest_messages), black_box(&weights)));
    });
}

criterion_group!(
    benches,
    block_new,
    block_from_prevblock_message,
    block_is_member,
    block_estimate,
);
criterion_main!(benches);
