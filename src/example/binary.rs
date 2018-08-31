use std::convert::{From};
use std::collections::{BTreeSet, HashSet};

use traits::{Estimate, Data, Zero};
use message::{CasperMsg, Message};
use justification::{Justification, SenderState};
use senders_weight::{SendersWeight};
use weight_unit::{WeightUnit};
type Validator = u32;

/// a genesis block should be a block with estimate Block with prevblock =
/// None and data. data will be the unique identifier of this blockchain

// #[derive(Clone, Default, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
// pub struct Binary(bool);

pub type BinaryMsg = Message<bool /*Estimate*/, Validator /*Sender*/>;

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash)]
pub struct Tx;

impl Data for bool {
    type Data = Self;
    fn is_valid(_data: &Self::Data) -> bool {
        true // FIXME
    }
}
impl Estimate for bool {
    type M = BinaryMsg;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        finalized_msg: Option<&Self::M>,
        senders_weights: &SendersWeight<
            <<Self as Estimate>::M as CasperMsg>::Sender,
        >,
        // in fact i could put the whole mempool inside of this proto_block and
        // search for a reasonable set of txs in this function that does not
        // conflict with the past blocks
        proto_block: Option<<Self as Data>::Data>,
    ) -> Self {
        let (true_w, false_w) = latest_msgs.iter().fold(
            (WeightUnit::ZERO, WeightUnit::ZERO),
            |(true_w, false_w), msg| {
                let sender_current = msg.get_sender();
                let sender_weight = senders_weights
                    .get_weight(sender_current)
                    .unwrap_or(WeightUnit::ZERO);
                if *msg.get_estimate() {
                    (true_w + sender_weight, false_w)
                }
                else {
                    (true_w, false_w + sender_weight)
                }
            },
        );
        if true_w >= false_w {
            true
        }
        else {
            false
        }
    }
}
