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
        *current_msg.unwrap().get_estimate()
    }
}
