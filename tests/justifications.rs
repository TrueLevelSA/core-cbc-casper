extern crate casper;

use std::collections::HashSet;

use casper::justification::{Justification, LatestMsgs, SenderState};
use casper::message::{self, Trait};
use casper::util::weight::SendersWeight;

mod common;
use common::vote_count::VoteCount;

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
    let mut sender_state = SenderState {
        senders_weights: senders_weights.clone(),
        state_fault_weight: 0.0,
        my_last_msg: None,
        thr: 3.0,
        equivocators: HashSet::new(),
        latest_msgs: LatestMsgs::new(),
    };
    let mut j = Justification::new();
    let _ = sender_state.latest_msgs.update(v0);
    let _ = sender_state.latest_msgs.update(v1);
    let _ = sender_state.latest_msgs.update(v2);
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
    assert_eq!(sender_state.state_fault_weight, 3.0);
}

#[test]
fn faulty_inserts() {
    let senders_weights =
        SendersWeight::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
    let v0 = &VoteCount::create_vote_msg(0, false);
    let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
    let v1 = &VoteCount::create_vote_msg(1, true);
    let mut j0 = Justification::new();

    let sender_state = SenderState {
        senders_weights: senders_weights.clone(),
        state_fault_weight: (0.0),
        my_last_msg: None,
        thr: 0.0,
        equivocators: HashSet::new(),
        latest_msgs: LatestMsgs::new(),
    };

    let (success, sender_state) = j0.faulty_inserts([v0].iter().cloned().collect(), &sender_state);
    assert!(success);

    let (m0, _weights) = &message::Message::from_msgs(0, vec![v0], &sender_state).unwrap();

    // let m0 = &message::Message::new(0, justification, estimate);
    let mut j1 = Justification::new();
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
        &SenderState {
            senders_weights: senders_weights.clone(),
            state_fault_weight: (0.0),
            my_last_msg: None,
            thr: 1.0,
            equivocators: HashSet::new(),
            latest_msgs: LatestMsgs::new(),
        },
    );
    assert!(success,
        "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set"
    );

    let (_, sender_state2) = j1.clone().faulty_insert(
        v0_prime,
        &SenderState {
            thr: 1.0,
            ..sender_state.clone()
        },
    );
    assert_eq!(
        sender_state2.state_fault_weight, 1.0,
        "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set, and thus the state_fault_weight should be incremented to 1.0"
    );

    let (success, _) = j1.clone().faulty_insert(
        v0_prime,
        &SenderState {
            state_fault_weight: (0.1),
            thr: 1.0,
            ..sender_state.clone()
        },
    );
    assert!(!success,
        "$v0_prime$ conflicts with $v0$ through $m0$, and we should not accept this fault as the fault threshold gets crossed for the set"
    );

    let (_, sender_state2) = j1.clone().faulty_insert(
        v0_prime,
        &SenderState {
            state_fault_weight: (0.1),
            thr: 1.0,
            ..sender_state.clone()
        },
    );
    assert_eq!(sender_state2.state_fault_weight, 0.1,
        "$v0_prime$ conflicts with $v0$ through $m0$, and we should NOT accept this fault as the fault threshold gets crossed for the set, and thus the state_fault_weight should not be incremented"
    );

    let (success, _) = j1.clone().faulty_insert(
        v0_prime,
        &SenderState {
            state_fault_weight: (1.0),
            thr: 2.0,
            ..sender_state.clone()
        },
    );
    assert!(success,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should accept this fault as the thr doesnt get crossed for the set"
    );

    let senders_weights = SendersWeight::new([].iter().cloned().collect());
    // bug found
    let (success, _) = j1.clone().faulty_insert(
        v0_prime,
        &SenderState {
            senders_weights: senders_weights.clone(),
            state_fault_weight: 1.0,
            thr: 2.0,
            ..sender_state.clone()
        },
    );
    assert!(
        !success,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity"
    );

    let (_, sender_state) = j1.clone().faulty_insert(
        v0_prime,
        &SenderState {
            senders_weights: senders_weights.clone(),
            state_fault_weight: (1.0),
            my_last_msg: None,
            thr: 2.0,
            equivocators: HashSet::new(),
            latest_msgs: LatestMsgs::new(),
        },
    );
    assert_eq!(
            sender_state.state_fault_weight,
        1.0,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity, and thus the state_fault_weight should be unchanged"
    );
}
