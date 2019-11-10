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
use casper::message::{self, Message};
use casper::validator;

#[test]
fn msg_equality() {
    // v0 and v0_prime are equivocating messages (first child of a fork).
    let v0 = &VoteCount::create_vote_msg(0, false);
    let v1 = &VoteCount::create_vote_msg(1, true);
    let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
    let v0_idem = &VoteCount::create_vote_msg(0, false);

    assert!(v0 == v0_idem, "v0 and v0_idem should be equal");
    assert!(v0 != v0_prime, "v0 and v0_prime should NOT be equal");
    assert!(v0 != v1, "v0 and v1 should NOT be equal");

    let validators_weights =
        validator::Weights::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());

    let validator_state = validator::State::new(
        validators_weights,
        0.0,
        None,
        LatestMsgs::empty(),
        0.0,
        HashSet::new(),
    );

    let mut j0 = Justification::empty();
    let failure = j0
        .faulty_inserts(
            &vec![v0].iter().cloned().collect(),
            &mut validator_state.clone(),
        )
        .is_empty();
    assert_eq!(failure, false);

    let m0 = Message::from_msgs(0, vec![v0], &mut validator_state.clone()).unwrap();
    // let m0 = &Message::new(0, justification, estimate);

    let mut j1 = Justification::empty();

    let failure = j1
        .faulty_inserts(
            &vec![v0].iter().cloned().collect(),
            &mut validator_state.clone(),
        )
        .is_empty();
    assert_eq!(failure, false);

    let failure = j1
        .faulty_inserts(
            &vec![&m0].iter().cloned().collect(),
            &mut validator_state.clone(),
        )
        .is_empty();
    assert_eq!(failure, false);

    let msg1 = Message::from_msgs(0, vec![v0], &mut validator_state.clone()).unwrap();
    let msg2 = Message::from_msgs(0, vec![v0], &mut validator_state.clone()).unwrap();
    assert!(msg1 == msg2, "messages should be equal");

    let msg3 = Message::from_msgs(0, vec![v0, &m0], &mut validator_state.clone()).unwrap();
    assert!(msg1 != msg3, "msg1 should be different than msg3");
}

#[test]
fn msg_depends() {
    let v0 = &VoteCount::create_vote_msg(0, false);
    let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote

    let validators_weights =
        validator::Weights::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());

    let validator_state = validator::State::new(
        validators_weights,
        0.0,
        None,
        LatestMsgs::empty(),
        0.0,
        HashSet::new(),
    );

    let mut j0 = Justification::empty();
    let failure = j0
        .faulty_inserts(
            &vec![v0].iter().cloned().collect(),
            &mut validator_state.clone(),
        )
        .is_empty();
    assert_eq!(failure, false);

    let m0 = Message::from_msgs(0, vec![v0], &mut validator_state.clone()).unwrap();

    assert!(
        !v0.depends(v0_prime),
        "v0 does NOT depends on v0_prime as they are equivocating"
    );
    assert!(
        !m0.depends(&m0),
        "m0 does NOT depends on itself directly, by our impl choice"
    );
    assert!(!m0.depends(v0_prime), "m0 depends on v0 directly");
    assert!(m0.depends(v0), "m0 depends on v0 directly");

    let mut j0 = Justification::empty();
    let failure = j0
        .faulty_inserts(
            &[v0].iter().cloned().collect(),
            &mut validator_state.clone(),
        )
        .is_empty();
    assert_eq!(failure, false);

    let m0 = Message::from_msgs(0, vec![v0], &mut validator_state.clone()).unwrap();

    let mut j1 = Justification::empty();
    let failure = j1
        .faulty_inserts(
            &[v0].iter().cloned().collect(),
            &mut validator_state.clone(),
        )
        .is_empty();
    assert_eq!(failure, false);

    let failure = j1
        .faulty_inserts(
            &[&m0].iter().cloned().collect(),
            &mut validator_state.clone(),
        )
        .is_empty();
    assert_eq!(failure, false);

    let m1 = Message::from_msgs(0, vec![v0, &m0], &mut validator_state.clone()).unwrap();

    assert!(m1.depends(&m0), "m1 DOES depent on m0");
    assert!(!m0.depends(&m1), "but m0 does NOT depend on m1");
    assert!(m1.depends(v0), "m1 depends on v0 through m0");
}

#[test]
fn msg_equivocates() {
    let v0 = &VoteCount::create_vote_msg(0, false);
    let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
    let v1 = &VoteCount::create_vote_msg(1, true);

    let validators_weights =
        validator::Weights::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
    let validator_state = validator::State::new(
        validators_weights,
        0.0,
        None,
        LatestMsgs::empty(),
        0.0,
        HashSet::new(),
    );

    let mut j0 = Justification::empty();
    let failure = j0
        .faulty_inserts(
            &vec![v0].iter().cloned().collect(),
            &mut validator_state.clone(),
        )
        .is_empty();
    assert_eq!(failure, false);

    let m0 = Message::from_msgs(0, vec![v0], &mut validator_state.clone()).unwrap();

    let m1 = Message::from_msgs(1, vec![v0], &mut validator_state.clone()).unwrap();
    assert!(!v0.equivocates(v0), "should be all good");
    assert!(!v1.equivocates(&m0), "should be all good");
    assert!(!m0.equivocates(v1), "should be all good");
    assert!(v0.equivocates(v0_prime), "should be a direct equivocation");

    assert!(
        m0.equivocates(v0_prime),
        "should be an indirect equivocation, equivocates to m0 through v0"
    );
    assert!(
        m1.equivocates_indirect(v0_prime, HashSet::new()).0,
        "should be an indirect equivocation, equivocates to m0 through v0"
    );
}

#[test]
fn from_msgs() {
    let v0 = VoteCount::create_vote_msg(0, false);
    let v1 = VoteCount::create_vote_msg(1, false);
    let v2 = VoteCount::create_vote_msg(2, true);

    let res = Message::from_msgs(
        0,
        vec![&v0, &v1, &v2],
        &mut validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            None,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        ),
    )
    .expect("No errors expected");

    assert_eq!(*res.estimate(), VoteCount { yes: 1, no: 2 });
    assert_eq!(*res.sender(), 0);
    assert!(res
        .justification()
        .iter()
        .all(|m| vec![&v0, &v1, &v2].contains(&m)));
}

#[test]
fn from_msgs_only_equivocations() {
    let v0 = VoteCount::create_vote_msg(0, false);
    let v0_prime = VoteCount::create_vote_msg(0, true);

    let mut latest_msgs = LatestMsgs::empty();
    latest_msgs.update(&v0);

    let res = Message::<VoteCount>::from_msgs(
        0,
        vec![&v0_prime],
        &mut validator::State::new(
            validator::Weights::new(vec![(0, 1.0)].into_iter().collect()),
            0.0,
            None,
            latest_msgs,
            0.0,
            HashSet::new(),
        ),
    );
    match res {
        Err(message::Error::NoNewMessage) => (),
        _ => panic!("Expected NoNewMessage"),
    }
}

// #[test]
// fn set_as_final() {
//     let validator0 = 0;
//     let validator1 = 1;
//     let validators_weights = validator::Weights::new(
//         [(validator0, 1.0), (validator1, 1.0)].iter().cloned().collect(),
//     );
//     let validator_state = validator::State::new(
//         validators_weights.clone(),
//         0.0,
//         None,
//         LatestMsgs::empty(),
//         0.0,
//         HashSet::new(),
//     );
//     let validators = &validators_weights.validators().unwrap();

//     // validator0        v0---m0        m2---
//     // validator1               \--m1--/
//     let v0 = &VoteCount::create_vote_msg(validator1, false);
//     let safe_msgs = v0.get_msg_for_proposition(validators);
//     assert_eq!(safe_msgs.len(), 0, "only validator0 saw v0");

//     let (m0, validator_state) = &mut Message::from_msgs(
//         validator0,
//         vec![v0],
//         None,
//         &validator_state,
//         None as Option<VoteCount>,
//     ).unwrap();

//     let (m1, validator_state) = &Message::from_msgs(
//         validator1,
//         vec![m0],
//         None,
//         &validator_state,
//         None as Option<VoteCount>,
//     ).unwrap();

//     let (m2, _) = &Message::from_msgs(
//         validator0,
//         vec![m1],
//         None,
//         &validator_state,
//         None as Option<VoteCount>,
//     ).unwrap();

//     let safe_msgs = m2.get_msg_for_proposition(validators);

//     assert!(safe_msgs.len() == 1);
//     println!("------------");
//     println!("message before trimmed by set_as_final\n {:?}", m0);
//     m0.set_as_final();
//     println!("message after\n {:?}", m0);
//     println!("------------");
// }
