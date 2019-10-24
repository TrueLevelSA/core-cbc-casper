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

mod common;
use common::vote_count::VoteCount;

use std::collections::HashSet;

use casper::justification::{Justification, LatestMsgs};
use casper::message;
use casper::validator;

macro_rules! float_eq {
    ($lhs:expr, $rhs:expr) => {{
        assert!(
            f32::abs($lhs - $rhs) < std::f32::EPSILON,
            format!("float_eq: {} and {} aren't equal", $lhs, $rhs),
        )
    }};
    ($lhs:expr, $rhs:expr, $message:expr) => {{
        assert!(
            f32::abs($lhs - $rhs) < std::f32::EPSILON,
            format!(
                "float_eq: {} and {} aren't equal. Provided message: {}",
                $lhs, $rhs, $message
            ),
        )
    }};
}

#[test]
fn faulty_inserts_sorted() {
    let validators_weights =
        validator::Weights::new([(0, 1.0), (1, 2.0), (2, 3.0)].iter().cloned().collect());

    let v0 = &VoteCount::create_vote_msg(0, false);
    let v0_prime = &VoteCount::create_vote_msg(0, true);
    let v1 = &VoteCount::create_vote_msg(1, true);
    let v1_prime = &VoteCount::create_vote_msg(1, false);
    let v2 = &VoteCount::create_vote_msg(2, true);
    let v2_prime = &VoteCount::create_vote_msg(2, false);

    let mut latest_msgs = LatestMsgs::empty();
    latest_msgs.update(v0);
    latest_msgs.update(v1);
    latest_msgs.update(v2);

    let mut validator_state = validator::State::new(
        validators_weights.clone(),
        0.0,
        None,
        latest_msgs,
        3.0,
        HashSet::new(),
    );
    let mut j = Justification::empty();
    let sorted_msgs = validator_state
        .sort_by_faultweight(&vec![v2_prime, v1_prime, v0_prime].iter().cloned().collect());
    sorted_msgs.iter().for_each(|&m| {
        j.faulty_insert(m, &mut validator_state);
    });
    assert!(j.contains(v0_prime));
    assert!(j.contains(v1_prime));
    assert!(!j.contains(v2_prime));
    float_eq!(validator_state.fault_weight(), 3.0);
}

#[test]
fn faulty_inserts() {
    let validators_weights =
        validator::Weights::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
    let v0 = &VoteCount::create_vote_msg(0, false);
    let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
    let v1 = &VoteCount::create_vote_msg(1, true);
    let mut j0 = Justification::empty();

    let mut validator_state = validator::State::new(
        validators_weights.clone(),
        0.0,
        None,
        LatestMsgs::empty(),
        0.0,
        HashSet::new(),
    );

    let failure = j0
        .faulty_inserts(&[v0].iter().cloned().collect(), &mut validator_state)
        .is_empty();
    assert_eq!(failure, false);

    let m0 = message::Message::from_msgs(0, vec![v0], &mut validator_state.clone()).unwrap();

    // let m0 = &message::Message::new(0, justification, estimate);
    let mut j1 = Justification::empty();
    let failure = j1
        .faulty_inserts(&vec![v1].iter().cloned().collect(), &mut validator_state)
        .is_empty();
    assert_eq!(failure, false);

    let failure = j1
        .faulty_inserts(&vec![&m0].iter().cloned().collect(), &mut validator_state)
        .is_empty();
    assert_eq!(failure, false);

    let success = j1.faulty_insert(v0_prime, &mut validator_state);
    assert!(
        !success,
        "$v0_prime$ should conflict with $v0$ through $m0$, and we should reject as our fault tolerance thr is zero"
    );

    let mut state = validator::State::new_with_default_state(
        validator_state.clone(),
        None,
        None,
        None,
        None,
        Some(1.0),
        None,
    );
    let success = j1.clone().faulty_insert(v0_prime, &mut state);
    assert!(success,
        "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set"
    );

    let mut validator_state2 = validator::State::new_with_default_state(
        validator_state.clone(),
        None,
        None,
        None,
        None,
        Some(1.0),
        None,
    );
    j1.clone().faulty_insert(v0_prime, &mut validator_state2);
    float_eq!(
        validator_state2.fault_weight(), 1.0,
        "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set, and thus the state_fault_weight should be incremented to 1.0"
    );

    let mut state = validator::State::new_with_default_state(
        validator_state.clone(),
        None,
        Some(0.1),
        None,
        None,
        Some(1.0),
        None,
    );
    let success = j1.clone().faulty_insert(v0_prime, &mut state);
    assert!(!success,
        "$v0_prime$ conflicts with $v0$ through $m0$, and we should not accept this fault as the fault threshold gets crossed for the set"
    );

    let mut validator_state2 = validator::State::new_with_default_state(
        validator_state.clone(),
        None,
        Some(0.1),
        None,
        None,
        Some(1.0),
        None,
    );
    j1.clone().faulty_insert(v0_prime, &mut validator_state2);
    float_eq!(validator_state2.fault_weight(), 0.1,
        "$v0_prime$ conflicts with $v0$ through $m0$, and we should NOT accept this fault as the fault threshold gets crossed for the set, and thus the state_fault_weight should not be incremented"
    );

    let mut state = validator::State::new_with_default_state(
        validator_state.clone(),
        None,
        Some(1.0),
        None,
        None,
        Some(2.0),
        None,
    );
    let success = j1.clone().faulty_insert(v0_prime, &mut state);
    assert!(success,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should accept this fault as the thr doesnt get crossed for the set"
    );

    let validators_weights = validator::Weights::new([].iter().cloned().collect());
    // bug found
    let mut state = validator::State::new_with_default_state(
        validator_state.clone(),
        Some(validators_weights.clone()),
        Some(1.0),
        None,
        None,
        Some(2.0),
        None,
    );
    let success = j1.clone().faulty_insert(v0_prime, &mut state);
    assert!(
        !success,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the validator, which could be Infinity"
    );

    let mut validator_state = validator::State::new(
        validators_weights.clone(),
        1.0,
        None,
        LatestMsgs::empty(),
        2.0,
        HashSet::new(),
    );
    j1.clone().faulty_insert(v0_prime, &mut validator_state);
    float_eq!(
        validator_state.fault_weight(),
        1.0,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the validator, which could be Infinity, and thus the state_fault_weight should be unchanged"
    );
}
