extern crate casper;

use std::collections::HashSet;

use casper::justification::{Justification, LatestMsgs, LatestMsgsHonest, SenderState};
use casper::message::Trait;
use casper::senders_weight::SendersWeight;
use casper::traits::Estimate;

mod common;
use common::integer::*;

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

    assert_eq!(
        IntegerWrapper::mk_estimate(
            &LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(&Justification::new()),
                sender_state.equivocators()
            ),
            &senders_weights,
        ),
        Err("no msg")
    );

    let m0 = IntegerMsg::new(senders[0], Justification::new(), IntegerWrapper(1), None);
    let m1 = IntegerMsg::new(senders[1], Justification::new(), IntegerWrapper(2), None);
    let m2 = IntegerMsg::new(senders[2], Justification::new(), IntegerWrapper(3), None);
    let (m3, _) = IntegerMsg::from_msgs(senders[0], vec![&m0, &m1], &sender_state).unwrap();

    let (mut j0, _) = Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m2, &sender_state);
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(2)
    );

    j0.faulty_insert(&m3, &sender_state);
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

    assert_eq!(
        IntegerWrapper::mk_estimate(
            &LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(&Justification::new()),
                sender_state.equivocators()
            ),
            &senders_weights,
        ),
        Err("no msg")
    );

    let m0 = IntegerMsg::new(senders[0], Justification::new(), IntegerWrapper(1), None);
    let m1 = IntegerMsg::new(senders[1], Justification::new(), IntegerWrapper(2), None);
    let m2 = IntegerMsg::new(senders[2], Justification::new(), IntegerWrapper(3), None);
    let (m3, _) = IntegerMsg::from_msgs(senders[0], vec![&m0, &m1], &sender_state).unwrap();

    let (mut j0, _) = Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m2, &sender_state);
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m3, &sender_state);
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

    assert_eq!(
        IntegerWrapper::mk_estimate(
            &LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(&Justification::new()),
                sender_state.equivocators()
            ),
            &senders_weights,
        ),
        Err("no msg")
    );

    let m0 = IntegerMsg::new(senders[0], Justification::new(), IntegerWrapper(1), None);
    let m1 = IntegerMsg::new(senders[1], Justification::new(), IntegerWrapper(2), None);
    let m2 = IntegerMsg::new(senders[2], Justification::new(), IntegerWrapper(3), None);
    let m3 = IntegerMsg::new(senders[3], Justification::new(), IntegerWrapper(4), None);

    let (m4, _) =
        IntegerMsg::from_msgs(senders[3], vec![&m0, &m1, &m2, &m3], &sender_state).unwrap();

    let (mut j0, _) = Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(1)
    );

    j0.faulty_insert(&m2, &sender_state);
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(2)
    );

    j0.faulty_insert(&m3, &sender_state);
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(4)
    );

    j0.faulty_insert(&m4, &sender_state);
    assert_eq!(
        j0.mk_estimate(sender_state.equivocators(), &senders_weights)
            .unwrap(),
        IntegerWrapper(4)
    );
}
