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
use common::vote_count::VoteCount;

use std::collections::HashSet;

use casper::justification::{Justification, LatestMsgs};
use casper::message::{self, Trait};
use casper::sender;
use casper::util::weight::SendersWeight;

#[test]
fn faulty_inserts_sorted() {
    let senders_weights =
        SendersWeight::new([(0, 1.0), (1, 2.0), (2, 3.0)].iter().cloned().collect());

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

    let sender_state = sender::State::new(
        senders_weights.clone(),
        0.0,
        None,
        latest_msgs,
        3.0,
        HashSet::new(),
    );
    let mut j = Justification::empty();
    let sorted_msgs = sender_state
        .sort_by_faultweight(vec![v2_prime, v1_prime, v0_prime].iter().cloned().collect());
    let (_, sender_state) =
        sorted_msgs
            .iter()
            .fold((false, sender_state), |(success, sender_state), &m| {
                let (s, w) = j.faulty_insert(m, &sender_state);
                (s || success, w)
            });
    assert!(j.contains(v0_prime));
    assert!(j.contains(v1_prime));
    assert!(!j.contains(v2_prime));
    assert_eq!(sender_state.fault_weight(), 3.0);
}

#[test]
fn faulty_inserts() {
    let senders_weights =
        SendersWeight::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
    let v0 = &VoteCount::create_vote_msg(0, false);
    let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
    let v1 = &VoteCount::create_vote_msg(1, true);
    let mut j0 = Justification::empty();

    let sender_state = sender::State::new(
        senders_weights.clone(),
        0.0,
        None,
        LatestMsgs::empty(),
        0.0,
        HashSet::new(),
    );

    let (success, sender_state) = j0.faulty_inserts([v0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (m0, _weights) = &message::Message::from_msgs(0, vec![v0], &sender_state).unwrap();

    // let m0 = &message::Message::new(0, justification, estimate);
    let mut j1 = Justification::empty();
    let (success, sender_state) =
        j1.faulty_inserts(vec![v1].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (success, sender_state) =
        j1.faulty_inserts(vec![m0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (success, sender_state) = j1.faulty_insert(v0_prime, &sender_state);
    assert!(
        !success,
        "$v0_prime$ should conflict with $v0$ through $m0$, and we should reject as our fault tolerance thr is zero"
    );

    let (success, _) = j1.clone().faulty_insert(
        v0_prime,
        &sender::State::from_state(
            sender_state.clone(),
            None,
            None,
            None,
            None,
            Some(1.0),
            None,
        ),
    );
    assert!(success,
        "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set"
    );

    let (_, sender_state2) = j1.clone().faulty_insert(
        v0_prime,
        &sender::State::from_state(
            sender_state.clone(),
            None,
            None,
            None,
            None,
            Some(1.0),
            None,
        ),
    );
    assert_eq!(
        sender_state2.fault_weight(), 1.0,
        "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set, and thus the state_fault_weight should be incremented to 1.0"
    );

    let (success, _) = j1.clone().faulty_insert(
        v0_prime,
        &sender::State::from_state(
            sender_state.clone(),
            None,
            Some(0.1),
            None,
            None,
            Some(1.0),
            None,
        ),
    );
    assert!(!success,
        "$v0_prime$ conflicts with $v0$ through $m0$, and we should not accept this fault as the fault threshold gets crossed for the set"
    );

    let (_, sender_state2) = j1.clone().faulty_insert(
        v0_prime,
        &sender::State::from_state(
            sender_state.clone(),
            None,
            Some(0.1),
            None,
            None,
            Some(1.0),
            None,
        ),
    );
    assert_eq!(sender_state2.fault_weight(), 0.1,
        "$v0_prime$ conflicts with $v0$ through $m0$, and we should NOT accept this fault as the fault threshold gets crossed for the set, and thus the state_fault_weight should not be incremented"
    );

    let (success, _) = j1.clone().faulty_insert(
        v0_prime,
        &sender::State::from_state(
            sender_state.clone(),
            None,
            Some(1.0),
            None,
            None,
            Some(2.0),
            None,
        ),
    );
    assert!(success,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should accept this fault as the thr doesnt get crossed for the set"
    );

    let senders_weights = SendersWeight::new([].iter().cloned().collect());
    // bug found
    let (success, _) = j1.clone().faulty_insert(
        v0_prime,
        &sender::State::from_state(
            sender_state.clone(),
            Some(senders_weights.clone()),
            Some(1.0),
            None,
            None,
            Some(2.0),
            None,
        ),
    );
    assert!(
        !success,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity"
    );

    let (_, sender_state) = j1.clone().faulty_insert(
        v0_prime,
        &sender::State::new(
            senders_weights.clone(),
            1.0,
            None,
            LatestMsgs::empty(),
            2.0,
            HashSet::new(),
        ),
    );
    assert_eq!(
            sender_state.fault_weight(),
        1.0,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity, and thus the state_fault_weight should be unchanged"
    );
}
