use std::collections::{BTreeSet};
use traits::{Estimate, Data};
use message::{AbstractMsg, Message};
use justification::{Justification, Weights};

type Miner = u32;

#[derive(Clone, Default, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
struct Block {
    prev_block: ProtoBlock,
    data: Option<<ProtoBlock as AbstractMsg>::Data>,
}

type ProtoBlock = Message<Block /*estimate*/, Miner /*sender*/, Txs>;

// TODO: i think its possible to do ghost in arbitrary data, that is default implementation
impl Estimate for Block {
    type M = ProtoBlock;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        finalized_msg: Option<&Self::M>,
        weights: &Weights<Miner>,
        data: Option<<<Self as Estimate>::M as AbstractMsg>::Data>,
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
            .and_then(|(prev_block, _)| {
                Some(Block {
                    prev_block: prev_block.clone(),
                    data,
                })
            })
    }
}


#[derive(Eq, Ord, PartialOrd, PartialEq, Clone, Default, Hash, Debug)]
pub struct Tx;
pub type Txs = BTreeSet<Tx>;
impl Data for Txs {}

#[test]
fn blockchain() {
    let miner = 10;
    let prev_block = None;
    let justification = Justification::new();
    let genesis_block =
        ProtoBlock::new(miner, justification, prev_block.clone());
    assert_eq!(genesis_block.get_estimate(), prev_block, "hardcoded");
}
