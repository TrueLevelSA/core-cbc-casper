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

extern crate casper;

use std::collections::HashSet;

use casper::IntegerWrapper;

use casper::estimator::Estimator;
use casper::justification::{Justification, LatestMessages, LatestMessagesHonest};
use casper::message::Message;
use casper::validator;

#[test]
fn equal_weight() {
    let validators: Vec<u32> = (0..4).collect();
    let weights = [1.0, 1.0, 1.0, 1.0];

    let validators_weights = validator::Weights::new(
        validators
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let validator_state = validator::State::new(
        validators_weights.clone(),
        0.0,
        LatestMessages::empty(),
        1.0,
        HashSet::new(),
    );

    assert_eq!(
        IntegerWrapper::estimate(
            &LatestMessagesHonest::from_latest_messages(
                &LatestMessages::from(&Justification::empty()),
                validator_state.equivocators()
            ),
            &validators_weights,
        ),
        Err("no message".into())
    );

    let m0 = Message::new(validators[0], Justification::empty(), IntegerWrapper(1));
    let m1 = Message::new(validators[1], Justification::empty(), IntegerWrapper(2));
    let m2 = Message::new(validators[2], Justification::empty(), IntegerWrapper(3));
    let mut validator_state_clone = validator_state.clone();
    validator_state_clone.update(&[&m0, &m1, &m2]);
    let m3 = Message::from_validator_state(validators[0], &validator_state_clone).unwrap();

    let mut j0 = Justification::from_messages(vec![m0, m1], &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m2, &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(2)
    );

    j0.faulty_insert(&m3, &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(2)
    );
}

/// The first validator has most of the weight.
#[test]
fn uneven_weights_1() {
    let validators: Vec<u32> = (0..4).collect();
    let weights = [4.0, 1.0, 1.0, 1.0];

    let validators_weights = validator::Weights::new(
        validators
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let validator_state = validator::State::new(
        validators_weights.clone(),
        0.0,
        LatestMessages::empty(),
        1.0,
        HashSet::new(),
    );

    assert_eq!(
        IntegerWrapper::estimate(
            &LatestMessagesHonest::from_latest_messages(
                &LatestMessages::from(&Justification::empty()),
                validator_state.equivocators()
            ),
            &validators_weights,
        ),
        Err("no message".into())
    );

    let m0 = Message::new(validators[0], Justification::empty(), IntegerWrapper(1));
    let m1 = Message::new(validators[1], Justification::empty(), IntegerWrapper(2));
    let m2 = Message::new(validators[2], Justification::empty(), IntegerWrapper(3));
    let mut validator_state_clone = validator_state.clone();
    validator_state_clone.update(&[&m0, &m1, &m2]);
    let m3 = Message::from_validator_state(validators[0], &validator_state_clone).unwrap();

    let mut j0 = Justification::from_messages(vec![m0, m1], &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m2, &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m3, &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(1)
    );
}

/// The fourth validator has most of the weight.
#[test]
fn uneven_weights_4() {
    let validators: Vec<u32> = (0..4).collect();
    let weights = [1.0, 1.0, 1.0, 4.0];

    let validators_weights = validator::Weights::new(
        validators
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let validator_state = validator::State::new(
        validators_weights.clone(),
        0.0,
        LatestMessages::empty(),
        1.0,
        HashSet::new(),
    );

    assert_eq!(
        IntegerWrapper::estimate(
            &LatestMessagesHonest::from_latest_messages(
                &LatestMessages::from(&Justification::empty()),
                validator_state.equivocators()
            ),
            &validators_weights,
        ),
        Err("no message".into())
    );

    let m0 = Message::new(validators[0], Justification::empty(), IntegerWrapper(1));
    let m1 = Message::new(validators[1], Justification::empty(), IntegerWrapper(2));
    let m2 = Message::new(validators[2], Justification::empty(), IntegerWrapper(3));
    let m3 = Message::new(validators[3], Justification::empty(), IntegerWrapper(4));

    let mut validator_state_clone = validator_state.clone();
    validator_state_clone.update(&[&m0, &m1, &m2, &m3]);
    let m4 = Message::from_validator_state(validators[3], &validator_state_clone).unwrap();

    let mut j0 = Justification::from_messages(vec![m0, m1], &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m2, &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(2)
    );

    j0.faulty_insert(&m3, &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(4)
    );

    j0.faulty_insert(&m4, &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        IntegerWrapper(4)
    );
}
