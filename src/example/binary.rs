use traits::{Estimate, Data, Zero};
use message::{CasperMsg, Message};
use justification::{LatestMsgs};
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
        latest_msgs: &LatestMsgs<Self::M>,
        _finalized_msg: Option<&Self::M>,
        senders_weights: &SendersWeight<
            <<Self as Estimate>::M as CasperMsg>::Sender,
        >,
        _data: Option<<Self as Data>::Data>,
    ) -> Self {
        let (true_w, false_w) = latest_msgs.iter().fold(
            (WeightUnit::ZERO, WeightUnit::ZERO),
            |(true_w, false_w), (sender_current, msgs)| {
                let (true_w_intermediate, false_w_intermediate) =
                    msgs.iter().fold(
                        (WeightUnit::ZERO, WeightUnit::ZERO),
                        |(true_w, false_w), msg| {
                            let sender_weight = senders_weights
                                .get_weight(sender_current)
                                .unwrap_or(WeightUnit::ZERO);
                            if *msg.get_estimate() {
                                (true_w + sender_weight, false_w)
                            } else {
                                (true_w, false_w + sender_weight)
                            }
                        },
                    );
                (true_w + true_w_intermediate, false_w + false_w_intermediate)
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

    let weights = SenderState::new(
        senders_weights.clone(),
        0.0, // state fault weight
        LatestMsgs::new(),
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    let m0 = BinaryMsg::new(senders[0], Justification::new(), false);
    let m1 = BinaryMsg::new(senders[1], Justification::new(), true);
    let m2 = BinaryMsg::new(senders[2], Justification::new(), false);
    let (m3, _) =
        BinaryMsg::from_msgs(senders[0], vec![&m0, &m1], None, &weights, None)
            .unwrap();

    assert_eq!(
        bool::mk_estimate(
            &LatestMsgs::from(Justification::new()),
            None,
            &senders_weights,
            None
        ),
        true
    );
    let mut j0 = Justification::from_msgs(vec![m0.clone(), m1.clone()]);
    // s0 and s1 vote. since tie-breaker is `true`, get `true`
    assert_eq!(
        bool::mk_estimate(
            &LatestMsgs::from(j0.clone()),
            None,
            &senders_weights,
            None
        ),
        true
    );
    j0.insert(m2.clone());
    // `false` now has weight 2.0, while true has weight `1.0`
    assert_eq!(
        bool::mk_estimate(
            &LatestMsgs::from(j0.clone()),
            None,
            &senders_weights,
            None
        ),
        false
    );
    j0.insert(m3.clone());
    assert_eq!(
        bool::mk_estimate(
            &LatestMsgs::from(j0.clone()),
            None,
            &senders_weights,
            None
        ),
        true
    );
}
