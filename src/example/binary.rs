use traits::{Estimate, Data, Zero};
use message::{CasperMsg, Message};
use justification::{LatestMsgsHonest, LatestMsgs};
use senders_weight::{SendersWeight};
use weight_unit::{WeightUnit};
type Validator = u32;

pub type BinaryMsg = Message<bool /*Estimate*/, Validator /*Sender*/>;

impl Data for bool {
    type Data = Self;
    fn is_valid(_data: &Self::Data) -> bool {
        true // FIXME
    }
}
impl Estimate for bool {
    type M = BinaryMsg;
    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        _finalized_msg: Option<&Self::M>,
        senders_weights: &SendersWeight<
            <<Self as Estimate>::M as CasperMsg>::Sender,
        >,
        _data: Option<<Self as Data>::Data>,
    ) -> Self {
        let (true_w, false_w) = latest_msgs.iter().fold(
            (WeightUnit::ZERO, WeightUnit::ZERO),
            |(true_w, false_w), msg| {
                let sender_weight = senders_weights
                    .get_weight(msg.get_sender())
                    .unwrap_or(WeightUnit::ZERO);
                if *msg.get_estimate() {
                    (true_w + sender_weight, false_w)
                } else {
                    (true_w, false_w + sender_weight)
                }
            },
        );
        true_w >= false_w
    }
}

#[test]
fn equal_weight() {
    use senders_weight::SendersWeight;
    use justification::{SenderState,Justification};
    use std::collections::{HashSet};

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
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    let m0 = BinaryMsg::new(senders[0], Justification::new(), false);
    let m1 = BinaryMsg::new(senders[1], Justification::new(), true);
    let m2 = BinaryMsg::new(senders[2], Justification::new(), false);
    let (m3, _) = BinaryMsg::from_msgs(
        senders[0],
        vec![&m0, &m1],
        None,
        &sender_state,
        None,
    ).unwrap();

    assert_eq!(
        bool::mk_estimate(
            &LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(&Justification::new()),
                sender_state.get_equivocators()
            ),
            None,
            &senders_weights,
            None
        ),
        true
    );
    let (mut j0, _) =
        Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
    // s0 and s1 vote. since tie-breaker is `true`, get `true`
    assert_eq!(
        j0.mk_estimate(
            None,
            sender_state.get_equivocators(),
            &senders_weights,
            None
        ),
        true
    );
    j0.faulty_insert(&m2, &sender_state);
    // `false` now has weight 2.0, while true has weight `1.0`
    assert_eq!(
        j0.mk_estimate(
            None,
            sender_state.get_equivocators(),
            &senders_weights,
            None
        ),
        false
    );
    j0.faulty_insert(&m3, &sender_state);
    assert_eq!(
        j0.mk_estimate(
            None,
            sender_state.get_equivocators(),
            &senders_weights,
            None
        ),
        true
    );
}

#[test]
fn vote_swaying() {
    use senders_weight::SendersWeight;
    use justification::{SenderState,Justification};
    use std::collections::{HashSet};

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
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    let m0 = BinaryMsg::new(senders[0], Justification::new(), false);
    let m1 = BinaryMsg::new(senders[1], Justification::new(), true);
    let m2 = BinaryMsg::new(senders[2], Justification::new(), true);
    let m3 = BinaryMsg::new(senders[3], Justification::new(), false);
    let m4 = BinaryMsg::new(senders[4], Justification::new(), false);

    let (mut j0, _) = Justification::from_msgs(
        vec![m0.clone(), m1.clone(), m2.clone(), m3.clone(), m4.clone()],
        &sender_state,
    );

    // honest result of vote: false
    assert_eq!(
        j0.mk_estimate(
            None,
            sender_state.get_equivocators(),
            &senders_weights,
            None
        ),
        false
    );

    // assume sender 0 has seen messages from sender 1 and sender 2 and reveals this in a published message
    let (m5, _) = BinaryMsg::from_msgs(
        senders[0],
        vec![&m0, &m1, &m2],
        None,
        &sender_state,
        None,
    ).unwrap();

    j0.faulty_insert(&m5, &sender_state);
    // sender 0 now "votes" in the other direction and sways the result: true
    assert_eq!(
        j0.mk_estimate(
            None,
            sender_state.get_equivocators(),
            &senders_weights,
            None
        ),
        true
    );
}
