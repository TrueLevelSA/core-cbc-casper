use traits::{Estimate, Data, Zero};
use message::{CasperMsg, Message};
use justification::{LatestMsgsHonest};
use senders_weight::{SendersWeight};
use weight_unit::{WeightUnit};
use std::collections::HashSet;
use std::iter::FromIterator;
type Validator = u32;

pub type IntegerMsg = Message<u32 /*Estimate*/, Validator /*Sender*/>;

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash)]
pub struct Tx;

impl Data for u32 {
    type Data = Self;
    fn is_valid(_data: &Self::Data) -> bool {
        true // FIXME
    }
}

impl Estimate for u32 {
    type M = IntegerMsg;

    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        _finalized_msg: Option<&Self::M>,
        senders_weights: &SendersWeight<
            <<Self as Estimate>::M as CasperMsg>::Sender,
        >,
        // in fact i could put the whole mempool inside of this proto_block and
        // search for a reasonable set of txs in this function that does not
        // conflict with the past blocks
        _proto_block: Option<<Self as Data>::Data>,
    ) -> Self {
        let mut msgs_sorted_by_estimate =
            Vec::from_iter(latest_msgs.iter().fold(
                HashSet::new(),
                |mut latest, latest_from_validator| {
                    latest.insert(latest_from_validator);
                    latest
                },
            ));
        msgs_sorted_by_estimate.sort_unstable_by(|a, b| {
            a.get_estimate().cmp(&b.get_estimate())
        });
        let total_weight = msgs_sorted_by_estimate.iter().fold(
            WeightUnit::ZERO,
            |acc, x| {
                acc + senders_weights
                    .get_weight(x.get_sender())
                    .unwrap_or(WeightUnit::ZERO)
            },
        );
        let mut running_weight = 0.0;
        let mut msg_iter = msgs_sorted_by_estimate.iter();
        let mut current_msg:Result<&&IntegerMsg, &str> = Err("no msg");
        while running_weight / total_weight < 0.5 {
            current_msg = msg_iter.next().ok_or("no next msg");
            running_weight +=
                current_msg
                .and_then(|m| senders_weights.get_weight(m.get_sender()))
                .unwrap_or(WeightUnit::ZERO)
        }
        match current_msg {
            Err(_) => 0,
            Ok(m) => *m.get_estimate()
        }
    }
}

#[cfg(test)]
mod tests{
    use std::collections::{HashSet};

    use super::*;
    use senders_weight::SendersWeight;
    use justification::{SenderState, Justification, LatestMsgs};

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
            u32::mk_estimate(
                &LatestMsgsHonest::from_latest_msgs(
                    &LatestMsgs::from(&Justification::new()),
                    sender_state.get_equivocators()
                ),
                None,
                &senders_weights,
                None
            ),
            0
        );

        let m0 = IntegerMsg::new(senders[0], Justification::new(), 1);
        let m1 = IntegerMsg::new(senders[1], Justification::new(), 2);
        let m2 = IntegerMsg::new(senders[2], Justification::new(), 3);
        let (m3, _) = IntegerMsg::from_msgs(
            senders[0],
            vec![&m0, &m1],
            None,
            &sender_state,
            None,
        ).unwrap();

        let (mut j0, _) =
            Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            1
        );

        j0.faulty_insert(&m2, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            2
        );

        j0.faulty_insert(&m3, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            2
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
            u32::mk_estimate(
                &LatestMsgsHonest::from_latest_msgs(
                    &LatestMsgs::from(&Justification::new()),
                    sender_state.get_equivocators()
                ),
                None,
                &senders_weights,
                None
            ),
            0
        );

        let m0 = IntegerMsg::new(senders[0], Justification::new(), 1);
        let m1 = IntegerMsg::new(senders[1], Justification::new(), 2);
        let m2 = IntegerMsg::new(senders[2], Justification::new(), 3);
        let (m3, _) = IntegerMsg::from_msgs(
            senders[0],
            vec![&m0, &m1],
            None,
            &sender_state,
            None,
        ).unwrap();

        let (mut j0, _) =
            Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            1
        );

        j0.faulty_insert(&m2, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            1
        );

        j0.faulty_insert(&m3, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            1
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
            u32::mk_estimate(
                &LatestMsgsHonest::from_latest_msgs(
                    &LatestMsgs::from(&Justification::new()),
                    sender_state.get_equivocators()
                ),
                None,
                &senders_weights,
                None
            ),
            0
        );

        let m0 = IntegerMsg::new(senders[0], Justification::new(), 1);
        let m1 = IntegerMsg::new(senders[1], Justification::new(), 2);
        let m2 = IntegerMsg::new(senders[2], Justification::new(), 3);
        let m3 = IntegerMsg::new(senders[3], Justification::new(), 4);

        let (m4, _) = IntegerMsg::from_msgs(
            senders[3],
            vec![&m0, &m1, &m2, &m3],
            None,
            &sender_state,
            None,
        ).unwrap();

        let (mut j0, _) =
            Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            1
        );

        j0.faulty_insert(&m2, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            2
        );

        j0.faulty_insert(&m3, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            4
        );

        j0.faulty_insert(&m4, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                &senders_weights,
                None
            ),
            4
        );

    }
}
