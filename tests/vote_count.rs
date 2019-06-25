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

// FIXME: this test is old and does not run anymore
//extern crate casper;
//
//use std::collections::HashSet;
//
//use casper::message::{self, Trait};
//use casper::traits::Estimate;
//use casper::justification::{Justification, LatestMsgs, LatestMsgsHonest, SenderState};
//use casper::senders_weight::SendersWeight;
//
//mod common;
//use common::vote_count::*;
//
//#[test]
//fn count_votes() {
//    let senders_weights =
//        SendersWeight::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
//
//    let v0 = &VoteCount::create_vote_msg(0, false);
//    let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
//    let v1 = &VoteCount::create_vote_msg(1, true);
//    let mut j0 = Justification::new();
//
//    let weights = SenderState::new(
//        senders_weights,
//        0.0,
//        None,
//        LatestMsgs::new(),
//        2.0,
//        HashSet::new(),
//    );
//
//    let (success, _) = j0.faulty_inserts(vec![v0].iter().cloned().collect(), &weights);
//    assert!(success);
//
//    let (m0, _) = &message::Message::from_msgs(0, vec![v0], None, &weights, None).unwrap();
//    let mut j1 = Justification::new();
//    let (success, _) = j1.faulty_inserts(vec![v1].iter().cloned().collect(), &weights);
//    assert!(success);
//
//    let (success, _) = j1.faulty_inserts(vec![m0].iter().cloned().collect(), &weights);
//    assert!(success);
//
//    let (m1, _) = &message::Message::from_msgs(1, vec![v1, m0], None, &weights, None).unwrap();
//    assert_eq!(
//        message::Message::estimate(m1).clone(),
//        VoteCount { yes: 1, no: 1 },
//        "should have 1 yes, and 1 no vote, found {:?}",
//        message::Message::estimate(m1).clone(),
//    );
//
//    let (success, _) = j1.faulty_inserts(vec![v0_prime].iter().cloned().collect(), &weights);
//    assert!(success);
//
//    let (m1_prime, _) = &message::Message::from_msgs(
//        1,
//        vec![v1, m0, v0_prime].iter().cloned().collect(),
//        None,
//        &weights,
//        None,
//    )
//    .unwrap();
//    assert_eq!(
//        message::Message::estimate(m1_prime).clone(),
//        VoteCount { yes: 1, no: 0 },
//        "should have 1 yes, and 0 no vote, found {:?}, the equivocation vote should cancels out the normal vote",
//        message::Message::estimate(&m1_prime).clone())
//}
