extern crate casper;

mod common;
use common::binary::*;

use std::collections::HashSet;

use casper::justification::{Justification, LatestMsgs, LatestMsgsHonest, SenderState};
use casper::message::Trait;
use casper::traits::Estimate;
use casper::util::weight::SendersWeight;

#[test]
fn equal_weight() {
    let senders: Vec<u32> = (0..4).collect();
    let weights = [1.0, 1.0, 1.0, 1.0];

    let senders_weights = SendersWeight::new(
        senders
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let sender_state = SenderState::new(
        senders_weights.clone(),
        0.0, // state fault weight
        None,
        LatestMsgs::new(),
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    let m0 = BinaryMsg::new(senders[0], Justification::new(), BoolWrapper(false), None);
    let m1 = BinaryMsg::new(senders[1], Justification::new(), BoolWrapper(true), None);
    let m2 = BinaryMsg::new(senders[2], Justification::new(), BoolWrapper(false), None);
    let (m3, _) = BinaryMsg::from_msgs(senders[0], vec![&m0, &m1], &sender_state).unwrap();

    assert_eq!(
        BoolWrapper::mk_estimate(
            &LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(&Justification::new()),
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

    let senders_weights = SendersWeight::new(
        senders
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let sender_state = SenderState::new(
        senders_weights.clone(),
        0.0, // state fault weight
        None,
        LatestMsgs::new(),
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    let m0 = BinaryMsg::new(senders[0], Justification::new(), BoolWrapper(false), None);
    let m1 = BinaryMsg::new(senders[1], Justification::new(), BoolWrapper(true), None);
    let m2 = BinaryMsg::new(senders[2], Justification::new(), BoolWrapper(true), None);
    let m3 = BinaryMsg::new(senders[3], Justification::new(), BoolWrapper(false), None);
    let m4 = BinaryMsg::new(senders[4], Justification::new(), BoolWrapper(false), None);

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
