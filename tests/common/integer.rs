use std::collections::HashSet;
use std::iter::FromIterator;

use casper::justification::LatestMsgsHonest;
use casper::message::{CasperMsg, Message};
use casper::senders_weight::SendersWeight;
use casper::traits::{Data, Estimate, Sender, Zero};
use casper::weight_unit::WeightUnit;

type Validator = u32;

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash, serde_derive::Serialize)]
pub struct IntegerWrapper(u32);

impl IntegerWrapper {
    pub fn new(estimate: u32) -> Self {
        IntegerWrapper(estimate)
    }
}

impl<S: Sender> From<S> for IntegerWrapper {
    fn from(_sender: S) -> Self {
        IntegerWrapper::new(u32::default())
    }
}

pub type IntegerMsg = Message<IntegerWrapper /*Estimate*/, Validator /*Sender*/>;

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash)]
pub struct Tx;

/// the goal here is to find the weighted median of all the values
impl Estimate for IntegerWrapper {
    type M = IntegerMsg;

    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        _finalized_msg: Option<&Self::M>,
        senders_weights: &SendersWeight<<<Self as Estimate>::M as CasperMsg>::Sender>,
        // in fact i could put the whole mempool inside of this proto_block and
        // search for a reasonable set of txs in this function that does not
        // conflict with the past blocks
        _proto_block: Option<<Self as Data>::Data>,
    ) -> Self {
        let mut msgs_sorted_by_estimate = Vec::from_iter(latest_msgs.iter().fold(
            HashSet::new(),
            |mut latest, latest_from_validator| {
                latest.insert(latest_from_validator);
                latest
            },
        ));
        msgs_sorted_by_estimate.sort_unstable_by(|a, b| a.get_estimate().cmp(&b.get_estimate()));

        // get the total weight of the senders of the messages
        // in the set
        let total_weight = msgs_sorted_by_estimate
            .iter()
            .fold(WeightUnit::ZERO, |acc, x| {
                acc + senders_weights
                    .get_weight(x.get_sender())
                    .unwrap_or(WeightUnit::ZERO)
            });

        let mut running_weight = 0.0;
        let mut msg_iter = msgs_sorted_by_estimate.iter();
        let mut current_msg: Result<&&IntegerMsg, &str> = Err("no msg");

        // since the messages are ordered according to their estimates,
        // whichever estimate is found after iterating over half of the total weight
        // is the consensus
        while running_weight / total_weight < 0.5 {
            current_msg = msg_iter.next().ok_or("no next msg");
            running_weight += current_msg
                .and_then(|m| senders_weights.get_weight(m.get_sender()))
                .unwrap_or(WeightUnit::ZERO)
        }

        // return said estimate
        match current_msg {
            Err(_) => IntegerWrapper(0),
            Ok(m) => m.get_estimate().clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use casper::justification::{Justification, LatestMsgs, SenderState};
    use casper::senders_weight::SendersWeight;

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
                    sender_state.get_equivocators()
                ),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(0)
        );

        let m0 = IntegerMsg::new(senders[0], Justification::new(), IntegerWrapper(1), None);
        let m1 = IntegerMsg::new(senders[1], Justification::new(), IntegerWrapper(2), None);
        let m2 = IntegerMsg::new(senders[2], Justification::new(), IntegerWrapper(3), None);
        let (m3, _) =
            IntegerMsg::from_msgs(senders[0], vec![&m0, &m1], None, &sender_state, None).unwrap();

        let (mut j0, _) = Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(1)
        );

        j0.faulty_insert(&m2, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(2)
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
                    sender_state.get_equivocators()
                ),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(0)
        );

        let m0 = IntegerMsg::new(senders[0], Justification::new(), IntegerWrapper(1), None);
        let m1 = IntegerMsg::new(senders[1], Justification::new(), IntegerWrapper(2), None);
        let m2 = IntegerMsg::new(senders[2], Justification::new(), IntegerWrapper(3), None);
        let (m3, _) =
            IntegerMsg::from_msgs(senders[0], vec![&m0, &m1], None, &sender_state, None).unwrap();

        let (mut j0, _) = Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(1)
        );

        j0.faulty_insert(&m2, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(1)
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
                    sender_state.get_equivocators()
                ),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(0)
        );

        let m0 = IntegerMsg::new(senders[0], Justification::new(), IntegerWrapper(1), None);
        let m1 = IntegerMsg::new(senders[1], Justification::new(), IntegerWrapper(2), None);
        let m2 = IntegerMsg::new(senders[2], Justification::new(), IntegerWrapper(3), None);
        let m3 = IntegerMsg::new(senders[3], Justification::new(), IntegerWrapper(4), None);

        let (m4, _) = IntegerMsg::from_msgs(
            senders[3],
            vec![&m0, &m1, &m2, &m3],
            None,
            &sender_state,
            None,
        )
        .unwrap();

        let (mut j0, _) = Justification::from_msgs(vec![m0.clone(), m1.clone()], &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(1)
        );

        j0.faulty_insert(&m2, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(2)
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
            IntegerWrapper(4)
        );

        j0.faulty_insert(&m4, &sender_state);
        assert_eq!(
            j0.mk_estimate(
                None,
                sender_state.get_equivocators(),
                None,
                &senders_weights,
                None
            ),
            IntegerWrapper(4)
        );
    }
}
