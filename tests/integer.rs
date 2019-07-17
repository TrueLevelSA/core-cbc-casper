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

// Explicitly allowing dead code here because of https://gitlab.com/TrueLevel/casper/core-cbc/issues/43
#[allow(dead_code)]
mod common;
use common::integer::*;

use std::collections::HashSet;

use casper::estimator::Estimator;
use casper::justification::{Justification, LatestMsgs, LatestMsgsHonest};
use casper::message::Trait;
use casper::sender;

#[test]
fn equal_weight() {
    let senders: Vec<u32> = (0..4).collect();
    let weights = [1.0, 1.0, 1.0, 1.0];

    let senders_weights = sender::Weights::new(
        senders
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let sender_state = sender::State::new(
        senders_weights.clone(),
        0.0, // state fault weight
        None,
        LatestMsgs::empty(),
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    assert_eq!(
        IntegerWrapper::estimate(
            &LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(&Justification::empty()),
                sender_state.equivocators()
            ),
            &senders_weights,
        ),
        Err("no msg")
    );

    let m0 = IntegerMsg::new(senders[0], Justification::empty(), IntegerWrapper(1));
    let m1 = IntegerMsg::new(senders[1], Justification::empty(), IntegerWrapper(2));
    let m2 = IntegerMsg::new(senders[2], Justification::empty(), IntegerWrapper(3));
    let m3 = IntegerMsg::from_msgs(senders[0], vec![&m0, &m1], &mut sender_state.clone()).unwrap();

    let mut j0 = Justification::from_msgs(vec![m0.clone(), m1.clone()], &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m2, &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(2)
    );

    j0.faulty_insert(&m3, &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(2)
    );
}

/// the 1st validator has most of the weight
#[test]
fn uneven_weights_1() {
    let senders: Vec<u32> = (0..4).collect();
    let weights = [4.0, 1.0, 1.0, 1.0];

    let senders_weights = sender::Weights::new(
        senders
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let sender_state = sender::State::new(
        senders_weights.clone(),
        0.0, // state fault weight
        None,
        LatestMsgs::empty(),
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    assert_eq!(
        IntegerWrapper::estimate(
            &LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(&Justification::empty()),
                sender_state.equivocators()
            ),
            &senders_weights,
        ),
        Err("no msg")
    );

    let m0 = IntegerMsg::new(senders[0], Justification::empty(), IntegerWrapper(1));
    let m1 = IntegerMsg::new(senders[1], Justification::empty(), IntegerWrapper(2));
    let m2 = IntegerMsg::new(senders[2], Justification::empty(), IntegerWrapper(3));
    let m3 = IntegerMsg::from_msgs(senders[0], vec![&m0, &m1], &mut sender_state.clone()).unwrap();

    let mut j0 = Justification::from_msgs(vec![m0.clone(), m1.clone()], &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m2, &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m3, &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(1)
    );
}

/// the 4th validator has most of the weight
#[test]
fn uneven_weights_4() {
    let senders: Vec<u32> = (0..4).collect();
    let weights = [1.0, 1.0, 1.0, 4.0];

    let senders_weights = sender::Weights::new(
        senders
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let sender_state = sender::State::new(
        senders_weights.clone(),
        0.0, // state fault weight
        None,
        LatestMsgs::empty(),
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    assert_eq!(
        IntegerWrapper::estimate(
            &LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(&Justification::empty()),
                sender_state.equivocators()
            ),
            &senders_weights,
        ),
        Err("no msg")
    );

    let m0 = IntegerMsg::new(senders[0], Justification::empty(), IntegerWrapper(1));
    let m1 = IntegerMsg::new(senders[1], Justification::empty(), IntegerWrapper(2));
    let m2 = IntegerMsg::new(senders[2], Justification::empty(), IntegerWrapper(3));
    let m3 = IntegerMsg::new(senders[3], Justification::empty(), IntegerWrapper(4));

    let m4 =
        IntegerMsg::from_msgs(senders[3], vec![&m0, &m1, &m2, &m3], &mut sender_state.clone()).unwrap();

    let mut j0 = Justification::from_msgs(vec![m0.clone(), m1.clone()], &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m2, &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(2)
    );

    j0.faulty_insert(&m3, &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(4)
    );

    j0.faulty_insert(&m4, &mut sender_state.clone());
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(4)
    );
}
