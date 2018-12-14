use justification::LatestMsgsHonest;
use message::{CasperMsg, Message};
use senders_weight::SendersWeight;
use traits::{Data, Estimate, Zero};
use weight_unit::WeightUnit;

type Validator = u32;

#[derive(Clone, Eq, PartialEq, Debug, Hash, serde_derive::Serialize)]
pub struct BoolWrapper(bool);

impl BoolWrapper {
    pub fn new(estimate: bool) -> Self {
        BoolWrapper(estimate)
    }
}

#[cfg(feature = "integration_test")]
impl<S: ::traits::Sender> From<S> for BoolWrapper {
    fn from(_sender: S) -> Self {
        BoolWrapper::new(bool::default())
    }
}

pub type BinaryMsg = Message<BoolWrapper /*Estimate*/, Validator /*Sender*/>;

impl Estimate for BoolWrapper {
    type M = BinaryMsg;

    /// weighted count of the votes contained in the latest messages
    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        _finalized_msg: Option<&Self::M>,
        senders_weights: &SendersWeight<<<Self as Estimate>::M as CasperMsg>::Sender>,
        _data: Option<<Self as Data>::Data>,
    ) -> Self {
        // loop over all the latest messages
        let (true_w, false_w) = latest_msgs.iter().fold(
            (WeightUnit::ZERO, WeightUnit::ZERO),
            |(true_w, false_w), msg| {
                // get the weight for the sender
                let sender_weight = senders_weights
                    .get_weight(msg.get_sender())
                    .unwrap_or(WeightUnit::ZERO);

                // add the weight to the right accumulator
                if msg.get_estimate().0.clone() {
                    (true_w + sender_weight, false_w)
                } else {
                    (true_w, false_w + sender_weight)
                }
            },
        );

        BoolWrapper(true_w >= false_w)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use justification::{Justification, LatestMsgs, SenderState};
    use senders_weight::SendersWeight;
    use std::collections::HashSet;

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
        let (m3, _) =
            BinaryMsg::from_msgs(senders[0], vec![&m0, &m1], None, &sender_state, None).unwrap();

        assert_eq!(
            BoolWrapper::mk_estimate(
                &LatestMsgsHonest::from_latest_msgs(
                    &LatestMsgs::from(&Justification::new()),
                    sender_state.get_equivocators()
                ),
                None,
                &senders_weights,
                None
            ),
            BoolWrapper(true)
        );
        let (mut j0, _) = Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
        // s0 and s1 vote. since tie-breaker is `true`, get `true`
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            BoolWrapper(true)
        );
        j0.faulty_insert(&m2, &sender_state);
        // `false` now has weight 2.0, while true has weight `1.0`
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            BoolWrapper(false)
        );
        j0.faulty_insert(&m3, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
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
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            BoolWrapper(false)
        );

        // assume sender 0 has seen messages from sender 1 and sender 2 and reveals this in a published message
        let (m5, _) =
            BinaryMsg::from_msgs(senders[0], vec![&m0, &m1, &m2], None, &sender_state, None)
                .unwrap();

        j0.faulty_insert(&m5, &sender_state);
        // sender 0 now "votes" in the other direction and sways the result: true
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            BoolWrapper(true)
        );
    }
}
