extern crate casper;

mod common;
use common::vote_count::VoteCount;

use std::collections::HashSet;

use casper::justification::{Justification, LatestMsgs, SenderState};
use casper::message::{Message, Trait};
use casper::util::weight::SendersWeight;

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

    let senders_weights =
        SendersWeight::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());

    let sender_state = SenderState::new(
        senders_weights,
        0.0,
        None,
        LatestMsgs::new(),
        0.0,
        HashSet::new(),
    );

    let mut j0 = Justification::new();
    let (success, _) = j0.faulty_inserts(vec![v0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (m0, _) = &Message::from_msgs(0, vec![v0], &sender_state).unwrap();
    // let m0 = &Message::new(0, justification, estimate);

    let mut j1 = Justification::new();

    let (success, _) = j1.faulty_inserts(vec![v0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (success, _) = j1.faulty_inserts(vec![m0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (msg1, _) = Message::from_msgs(0, vec![v0], &sender_state).unwrap();
    let (msg2, _) = Message::from_msgs(0, vec![v0], &sender_state).unwrap();
    assert!(msg1 == msg2, "messages should be equal");

    let (msg3, _) = Message::from_msgs(0, vec![v0, m0], &sender_state).unwrap();
    assert!(msg1 != msg3, "msg1 should be different than msg3");
}

#[test]
fn msg_depends() {
    let v0 = &VoteCount::create_vote_msg(0, false);
    let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote

    let senders_weights =
        SendersWeight::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());

    let sender_state = SenderState::new(
        senders_weights,
        0.0,
        None,
        LatestMsgs::new(),
        0.0,
        HashSet::new(),
    );

    let mut j0 = Justification::new();
    let (success, _) = j0.faulty_inserts(vec![v0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (m0, _) = &Message::from_msgs(0, vec![v0], &sender_state).unwrap();

    assert!(
        !v0.depends(v0_prime),
        "v0 does NOT depends on v0_prime as they are equivocating"
    );
    assert!(
        !m0.depends(m0),
        "m0 does NOT depends on itself directly, by our impl choice"
    );
    assert!(!m0.depends(v0_prime), "m0 depends on v0 directly");
    assert!(m0.depends(v0), "m0 depends on v0 directly");

    let mut j0 = Justification::new();
    let (success, _) = j0.faulty_inserts([v0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (m0, _) = &Message::from_msgs(0, vec![v0], &sender_state).unwrap();

    let mut j1 = Justification::new();
    let (success, _) = j1.faulty_inserts([v0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (success, _) = j1.faulty_inserts([m0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (m1, _) = &Message::from_msgs(0, vec![v0, m0], &sender_state).unwrap();

    assert!(m1.depends(m0), "m1 DOES depent on m0");
    assert!(!m0.depends(m1), "but m0 does NOT depend on m1");
    assert!(m1.depends(v0), "m1 depends on v0 through m0");
}

#[test]
fn msg_equivocates() {
    let v0 = &VoteCount::create_vote_msg(0, false);
    let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
    let v1 = &VoteCount::create_vote_msg(1, true);

    let senders_weights =
        SendersWeight::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
    let sender_state = SenderState::new(
        senders_weights,
        0.0,
        None,
        LatestMsgs::new(),
        0.0,
        HashSet::new(),
    );

    let mut j0 = Justification::new();
    let (success, _) = j0.faulty_inserts(vec![v0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (m0, _) = &Message::from_msgs(0, vec![v0], &sender_state).unwrap();

    let (m1, _) = &Message::from_msgs(1, vec![v0], &sender_state).unwrap();
    assert!(!v0.equivocates(v0), "should be all good");
    assert!(!v1.equivocates(m0), "should be all good");
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

// #[test]
// fn set_as_final() {
//     let sender0 = 0;
//     let sender1 = 1;
//     let senders_weights = SendersWeight::new(
//         [(sender0, 1.0), (sender1, 1.0)].iter().cloned().collect(),
//     );
//     let sender_state = SenderState::new(
//         senders_weights.clone(),
//         0.0,
//         None,
//         LatestMsgs::new(),
//         0.0,
//         HashSet::new(),
//     );
//     let senders = &senders_weights.senders().unwrap();

//     // sender0        v0---m0        m2---
//     // sender1               \--m1--/
//     let v0 = &VoteCount::create_vote_msg(sender1, false);
//     let safe_msgs = v0.get_msg_for_proposition(senders);
//     assert_eq!(safe_msgs.len(), 0, "only sender0 saw v0");

//     let (m0, sender_state) = &mut Message::from_msgs(
//         sender0,
//         vec![v0],
//         None,
//         &sender_state,
//         None as Option<VoteCount>,
//     ).unwrap();

//     let (m1, sender_state) = &Message::from_msgs(
//         sender1,
//         vec![m0],
//         None,
//         &sender_state,
//         None as Option<VoteCount>,
//     ).unwrap();

//     let (m2, _) = &Message::from_msgs(
//         sender0,
//         vec![m1],
//         None,
//         &sender_state,
//         None as Option<VoteCount>,
//     ).unwrap();

//     let safe_msgs = m2.get_msg_for_proposition(senders);

//     assert!(safe_msgs.len() == 1);
//     println!("------------");
//     println!("message before trimmed by set_as_final\n {:?}", m0);
//     m0.set_as_final();
//     println!("message after\n {:?}", m0);
//     println!("------------");
// }
