#[macro_use]
extern crate criterion;

use casper::estimator::Estimator;
use casper::justification::LatestMsgsHonest;
use casper::message;
use casper::util::weight::{WeightUnit, Zero};
use casper::validator;
use casper::Block;
use criterion::{black_box, Criterion};

type Validator = u8;
type Message = message::Message<Value>;

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

#[derive(Debug)]
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

impl Estimator for Value {
    type ValidatorName = Validator;
    type Error = Error;

    fn estimate<U: WeightUnit>(
        latest_msgs: &LatestMsgsHonest<Self>,
        validators_weights: &validator::Weights<Validator, U>,
    ) -> Result<Self, Self::Error> {
        let res: Self = latest_msgs
            .iter()
            .map(|msg| (msg.estimate(), validators_weights.weight(msg.sender())))
            .fold(
                (
                    (Value::Zero, <U as Zero<U>>::ZERO),
                    (Value::One, <U as Zero<U>>::ZERO),
                    (Value::Two, <U as Zero<U>>::ZERO),
                ),
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

fn block_new(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "Block::new",
        |b, loops| {
            b.iter(|| {
                let mut block: Option<Block<u8>> = None;
                for _ in 0..(**loops) {
                    block = Some(Block::new(block));
                }
            });
        },
        &[1_000, 10 * 1_000, 100 * 1_000],
    );
}

fn block_from_prevblock_msg(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "Block::from_prevblock_msg",
        |b, loops| {
            use std::collections::HashSet;

            use casper::justification::{Justification, LatestMsgs};

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
                validators_weights.clone(),
                0.0, // state fault weight
                LatestMsgs::empty(),
                1.0,            // subjective fault weight threshold
                HashSet::new(), // equivocators
            );
            let block: Block<u8> = Block::new(None);
            let mut msg = Message::new(1, Justification::empty(), Value::One);
            for _ in 0..=(**loops) {
                weights.update(&[&msg]);
                msg = Message::from_msgs(1, &weights).unwrap();
            }

            b.iter(|| {
                Block::from_prevblock_msg(black_box(None), black_box(block.clone()));
            });
        },
        &[100, 1_000, 10_000],
    );
}

fn block_is_member(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "Block::is_member",
        |b, loops| {
            let first_block: Block<u8> = Block::new(None);
            let mut block = Block::new(Some(first_block.clone()));
            for _ in 0..(**loops) {
                block = Block::new(Some(block));
            }
            b.iter(|| first_block.is_member(&block));
        },
        &[10, 100, 1_000],
    );
}

criterion_group!(
    benches,
    block_new,
    block_from_prevblock_msg,
    block_is_member
);
criterion_main!(benches);
