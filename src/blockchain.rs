use std::collections::{HashSet, BTreeSet};
use std::hash::{Hash};
use std::fmt::{Debug};

use traits::{Estimate, Data, Sender};
use message::{AbstractMsg, Message};
use justification::{Justification, Weights};
use senders_weight::{SendersWeight};
use std::sync::{Arc};

type Miner = u32;
type TxHash = u64;

#[derive(Clone, Default, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
struct BlockWrapped(Block);

type Block = Message<BlockWrapped /*estimate*/, Miner /*sender*/, Txs>;

// TODO: i think its possible to do ghost in arbitrary data, that is default implementation
impl Estimate for BlockWrapped {
    type M = Block;
    type Sender = Miner;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        finalized_msg: Option<&Self::M>,
        weights: &Weights<Miner>,
    ) -> Option<Self> {
        let senders_weights = weights.get_senders_weights();
        latest_msgs
            .get_children_weights(
                finalized_msg,
                senders_weights,
                &senders_weights.get_senders(),
            )
            .iter()
            .max_by(|(_, &weight0), (_, &weight1)| {
                weight1
                    .partial_cmp(&weight0)
                    // tie breaker, the unwrap fails because both values are the
                    // same and we arbitrarily chose a result
                    .unwrap_or(::std::cmp::Ordering::Greater)
            })
            .and_then(|(best_msg, _)| Some(BlockWrapped(best_msg.clone())))
    }
}

#[derive(Eq, Ord, PartialOrd, PartialEq, Clone, Default, Hash, Debug)]
pub struct Tx(TxHash);


pub type Txs = BTreeSet<Tx>;
impl Data for Txs {}

#[test]
fn blockchain() {
    let miner = 10;
    let prev_block = None;
    let justification = Justification::new();
    let genesis_block =
        Block::new(miner, justification, prev_block.clone());
    assert_eq!(genesis_block.get_estimate(), prev_block, "hardcoded");
}
