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

extern crate core_cbc_casper;

mod common;
use common::binary::*;

use std::collections::HashSet;

use core_cbc_casper::estimator::Estimator;
use core_cbc_casper::justification::{Justification, LatestMessages, LatestMessagesHonest};
use core_cbc_casper::message::Message;
use core_cbc_casper::validator;

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

    let m0 = Message::new(validators[0], Justification::empty(), BoolWrapper(false));
    let m1 = Message::new(validators[1], Justification::empty(), BoolWrapper(true));
    let m2 = Message::new(validators[2], Justification::empty(), BoolWrapper(false));
    let mut validator_state_clone = validator_state.clone();
    validator_state_clone.update(&[&m0, &m1]);
    let m3 = Message::from_validator_state(validators[0], &validator_state_clone).unwrap();

    assert_eq!(
        BoolWrapper::estimate(
            &LatestMessagesHonest::from_latest_messages(
                &LatestMessages::from(&Justification::empty()),
                validator_state.equivocators()
            ),
            &validators_weights,
        )
        .unwrap(),
        BoolWrapper(true)
    );
    let mut j0 = Justification::from_messages(vec![m0, m1], &mut validator_state.clone());
    // s0 and s1 vote. since tie-breaker is `true`, get `true`
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        BoolWrapper(true)
    );
    j0.faulty_insert(&m2, &mut validator_state.clone());
    // `false` now has weight 2.0, while true has weight `1.0`
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        BoolWrapper(false)
    );
    j0.faulty_insert(&m3, &mut validator_state.clone());
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        BoolWrapper(true)
    );
}

#[test]
fn vote_swaying() {
    let validators: Vec<u32> = (0..5).collect();
    let weights = [1.0, 1.0, 1.0, 1.0, 1.0];

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

    let m0 = Message::new(validators[0], Justification::empty(), BoolWrapper(false));
    let m1 = Message::new(validators[1], Justification::empty(), BoolWrapper(true));
    let m2 = Message::new(validators[2], Justification::empty(), BoolWrapper(true));
    let m3 = Message::new(validators[3], Justification::empty(), BoolWrapper(false));
    let m4 = Message::new(validators[4], Justification::empty(), BoolWrapper(false));

    let mut j0 = Justification::from_messages(
        vec![m0.clone(), m1.clone(), m2.clone(), m3, m4],
        &mut validator_state.clone(),
    );

    // Honest result of vote: false
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        BoolWrapper(false)
    );

    // Assume validator 0 has seen messages from validator 1 and validator 2 and reveals this in a
    // published message.
    let mut validator_state_clone = validator_state.clone();
    validator_state_clone.update(&[&m0, &m1, &m2]);
    let m5 = Message::from_validator_state(validators[0], &validator_state_clone).unwrap();

    j0.faulty_insert(&m5, &mut validator_state.clone());
    // Validator 0 now "votes" in the other direction and sways the result: true
    assert_eq!(
        j0.make_estimate(validator_state.equivocators(), &validators_weights)
            .unwrap(),
        BoolWrapper(true)
    );
}
