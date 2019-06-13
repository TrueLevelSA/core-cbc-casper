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

extern crate casper;

mod common;
use common::binary::*;

use std::collections::HashSet;

use casper::estimator::Estimate;
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

    let m0 = BinaryMsg::new(senders[0], Justification::empty(), BoolWrapper(false));
    let m1 = BinaryMsg::new(senders[1], Justification::empty(), BoolWrapper(true));
    let m2 = BinaryMsg::new(senders[2], Justification::empty(), BoolWrapper(false));
    let (m3, _) = BinaryMsg::from_msgs(senders[0], vec![&m0, &m1], &sender_state).unwrap();

    assert_eq!(
        BoolWrapper::mk_estimate(
            &LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(&Justification::empty()),
                sender_state.equivocators()
            ),
            &senders_weights,
        )
        .unwrap(),
        BoolWrapper(true)
    );
    let (mut j0, _) = Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
    // s0 and s1 vote. since tie-breaker is `true`, get `true`
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        BoolWrapper(true)
    );
    j0.faulty_insert(&m2, &sender_state);
    // `false` now has weight 2.0, while true has weight `1.0`
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        BoolWrapper(false)
    );
    j0.faulty_insert(&m3, &sender_state);
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        BoolWrapper(true)
    );
}

#[test]
fn vote_swaying() {
    let senders: Vec<u32> = (0..5).collect();
    let weights = [1.0, 1.0, 1.0, 1.0, 1.0];

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

    let m0 = BinaryMsg::new(senders[0], Justification::empty(), BoolWrapper(false));
    let m1 = BinaryMsg::new(senders[1], Justification::empty(), BoolWrapper(true));
    let m2 = BinaryMsg::new(senders[2], Justification::empty(), BoolWrapper(true));
    let m3 = BinaryMsg::new(senders[3], Justification::empty(), BoolWrapper(false));
    let m4 = BinaryMsg::new(senders[4], Justification::empty(), BoolWrapper(false));

    let (mut j0, _) = Justification::from_msgs(
        vec![m0.clone(), m1.clone(), m2.clone(), m3.clone(), m4.clone()],
        &sender_state,
    );

    // honest result of vote: false
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        BoolWrapper(false)
    );

    // assume sender 0 has seen messages from sender 1 and sender 2 and reveals this in a published message
    let (m5, _) = BinaryMsg::from_msgs(senders[0], vec![&m0, &m1, &m2], &sender_state).unwrap();

    j0.faulty_insert(&m5, &sender_state);
    // sender 0 now "votes" in the other direction and sways the result: true
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        BoolWrapper(true)
    );
}
