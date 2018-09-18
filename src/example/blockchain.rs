use std::fmt::{Debug, Formatter, Result as FmtResult};
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::convert::From;
use std::iter::Iterator;

use justification::{Justification, SenderState};
use message::{CasperMsg, Message};
use senders_weight::SendersWeight;
use std::sync::Arc;
use std::cmp::Ordering::{Equal, Greater, Less};
use traits::{Data, Estimate, Zero};
use weight_unit::WeightUnit;
type Validator = u32;

/// a genesis block should be a block with estimate Block with prevblock =
/// None and data. data will be the unique identifier of this blockchain

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
struct ProtoBlock {
    prevblock: Option<Block>,
    sender: Validator,
    txs: BTreeSet<Tx>,
}

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Debug)]
pub struct Block(Box<Arc<ProtoBlock>>);

pub type BlockMsg = Message<Block /*Estimate*/, Validator /*Sender*/>;

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash)]
pub struct Tx;

impl Data for Block {
    type Data = Self;
    fn is_valid(_data: &Self::Data) -> bool {
        true // FIXME
    }
}
//// this type can be used to create a look up for what msgs are referred by
//// what validators
// type ReferredValidators = HashMap<Block, HashSet<Validator>>;

impl From<ProtoBlock> for Block {
    fn from(protoblock: ProtoBlock) -> Self {
        Block(Box::new(Arc::new(protoblock)))
    }
}
impl<'z> From<&'z BlockMsg> for Block {
    fn from(msg: &BlockMsg) -> Self {
        msg.get_estimate().clone()
    }
}

impl Block {
    pub fn new(
        prevblock: Option<Block>,
        sender: Validator,
        txs: BTreeSet<Tx>,
    ) -> Self {
        Block::from(ProtoBlock {
            prevblock,
            sender,
            txs,
        })
    }
    pub fn get_txs(&self) -> &BTreeSet<Tx> {
        &self.0.txs
    }
    pub fn get_sender(&self) -> Validator {
        self.0.sender
    }
    pub fn from_prevblock_msg(
        prevblock_msg: Option<BlockMsg>,
        // a incomplete_block is a block with a None prevblock (ie, Estimate) AND is
        // not a genesis_block
        incomplete_block: Block,
    ) -> Result<Self, &'static str> {
        let prevblock = prevblock_msg.map(|m| Block::from(&m));
        let block = Block::from(ProtoBlock {
            prevblock,
            ..(**incomplete_block.0).clone()
        });

        if Block::is_valid(&block) {
            Ok(block)
        }
        else {
            Err("Block not valid")
        }
    }
    pub fn get_prevblock(&self) -> Option<Self> {
        self.0.prevblock.as_ref().cloned()
    }
    pub fn parse_blockchains(
        justification: &Justification<BlockMsg>,
        finalized_msg: Option<&BlockMsg>,
    ) -> (HashMap<Block, HashSet<Block>>, HashSet<Block>) {
        let mut visited: HashMap<Block, HashSet<Block>> = justification
            .iter()
            .map(|msg| {
                let parent = Block::from(msg);
                let children = HashSet::new();
                (parent, children)
            })
            .collect();
        let mut queue: VecDeque<Block> = visited.keys().cloned().collect();
        let mut genesis: HashSet<Block> = HashSet::new();
        while let Some(child) = queue.pop_front() {
            match child.get_prevblock() {
                Some(parent) => {
                    if visited.contains_key(&parent) {
                        // println!("visited parent before, fork found");
                        visited.get_mut(&parent).map(|parents_children| {
                            parents_children.insert(child);
                        });
                    }
                    else {
                        // println!("didnt visit parent before, set initial state, and push to queue");
                        let mut parents_children = HashSet::new();
                        parents_children.insert(child);
                        visited.insert(parent.clone(), parents_children);
                        queue.push_back(parent);
                    }
                },
                None => {
                    genesis.insert(child);
                },
            };
        }
        (visited, genesis)
    }

    // find heaviest block
    fn pick_heaviest(
        blocks: &HashSet<Block>,
        visited: &HashMap<Block, HashSet<Block>>,
        weights: &SendersWeight<Validator>,
    ) -> Option<(Option<Self>, WeightUnit, HashSet<Self>)> {
        let init = Some((None, WeightUnit::ZERO, HashSet::new()));
        let heaviest_child = blocks.iter().fold(init, |best, block| {
            best.and_then(|best| {
                visited.get(&block).map(|children| (best, children))
            }).map(|((b_block, b_weight, b_children), children)| {
                let mut referred_senders: HashSet<_> =
                    children.iter().map(Self::get_sender).collect();
                // add current block sender such that its weight counts too
                referred_senders.insert(block.get_sender());
                let weight = weights.sum_weight_senders(&referred_senders);
                // TODO: break ties with blockhash
                if weight > b_weight {
                    (Some(block.clone()), weight, children.clone())
                }
                else {
                    (b_block, b_weight, b_children)
                }
            })
        });
        heaviest_child.and_then(|(b_block, b_weight, b_children)| {
            if b_children.is_empty() {
                // base case
                Some((b_block, b_weight, b_children))
            }
            else {
                // recurse
                Self::pick_heaviest(&b_children, visited, &weights)
            }
        })
    }

    pub fn ghost(
        justification: &Justification<BlockMsg>,
        finalized_msg: Option<&BlockMsg>,
        senders_weights: &SendersWeight<<BlockMsg as CasperMsg>::Sender>,
    ) -> Option<Self> {
        let (visited, genesis) =
            Self::parse_blockchains(justification, finalized_msg);
        Block::pick_heaviest(&genesis, &visited, senders_weights)
            .and_then(|(opt_block, ..)| opt_block)
    }
}

impl Estimate for Block {
    type M = BlockMsg;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        finalized_msg: Option<&Self::M>,
        senders_weights: &SendersWeight<
            <<Self as Estimate>::M as CasperMsg>::Sender,
        >,
        // in fact i could put the whole mempool inside of this incomplete_block
        // and search for a reasonable set of txs in this function that does not
        // conflict with the past blocks
        incomplete_block: Option<<Self as Data>::Data>,
    ) -> Self {
        match (latest_msgs.len(), incomplete_block) {
            (0, _) => panic!(
                "Needs at least one latest message to be able to pick one"
            ),
            (_, None) => panic!("incomplete_block is None"),
            (1, Some(incomplete_block)) => {
                // only msg to built on top, no choice thus no ghost
                let msg = latest_msgs.iter().next().map(|msg| msg.clone());
                Self::from_prevblock_msg(msg, incomplete_block).unwrap()
            },
            (_, Some(incomplete_block)) => {
                let prevblock =
                    Block::ghost(latest_msgs, finalized_msg, senders_weights);
                let block = Block::from(ProtoBlock {
                    prevblock,
                    ..(**incomplete_block.0).clone()
                });
                block
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn example_usage() {
        let (sender0, sender1, sender2, sender3, sender4) = (0, 1, 2, 3, 4); // miner identities
        let (weight0, weight1, weight2, weight3, weight4) =
            (1.0, 1.0, 2.0, 1.0, 1.1); // and their corresponding weights
        let senders_weights = SendersWeight::new(
            [
                (sender0, weight0),
                (sender1, weight1),
                (sender2, weight2),
                (sender3, weight3),
                (sender4, weight4),
            ].iter()
                .cloned()
                .collect(),
        );
        let weights = SenderState::new(
            senders_weights.clone(),
            0.0,            // state fault weight
            1.0,            // subjective fault weight threshold
            HashSet::new(), // equivocators
        );

        let txs = BTreeSet::new();

        // msg dag
        // (s0, w=1.0)   gen            m5
        // (s1, w=1.0)    |\--m1---\    |
        // (s2, w=2.0)    \---m2--\|  --|
        // (s3, w=1.0)    |    \---m3---|
        // (s4, w=1.1)    \---m4

        // blockchain gen <--m2 <--m3
        // (s0, w=1.0)   gen            b5
        // (s1, w=1.0)    |\--b1
        // (s2, w=2.0)    \---b2
        // (s3, w=1.0)    |     \---b3

        // block dag
        let genesis_block = Block::from(ProtoBlock {
            prevblock: None,
            sender: sender0,
            txs: txs.clone(),
        });
        let justification = Justification::new();
        let genesis_block_msg =
            BlockMsg::new(sender0, justification, genesis_block.clone());
        assert_eq!(
            &Block::from(&genesis_block_msg),
            &genesis_block,
            "genesis block with None as prevblock"
        );
        let proto_b1 = Block::new(None, sender1, txs.clone());
        let (m1, weights) = BlockMsg::from_msgs(
            proto_b1.get_sender(),
            vec![&genesis_block_msg],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b1), // data
        ).unwrap();
        let proto_b2 = Block::new(None, sender2, txs.clone());
        let (m2, weights) = BlockMsg::from_msgs(
            proto_b2.get_sender(),
            vec![&genesis_block_msg],
            None,
            &weights,
            Some(proto_b2),
        ).unwrap();
        let proto_b3 = Block::new(None, sender3, txs.clone());
        let (m3, weights) = BlockMsg::from_msgs(
            proto_b3.get_sender(),
            vec![&m1, &m2],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b3),
        ).unwrap();

        assert_eq!(
            m3.get_estimate(),
            &Block::new(Some(Block::from(&m2)), sender3, txs.clone()),
            "should build on top of m2 as sender2 has more weight"
        );

        let proto_b4 = Block::new(None, sender4, txs.clone());
        let (m4, weights) = BlockMsg::from_msgs(
            proto_b4.get_sender(),
            vec![&m1],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b4),
        ).unwrap();

        assert_eq!(
            m4.get_estimate(),
            &Block::new(Some(Block::from(&m1)), sender4, txs.clone()),
            "should build on top of m1 as as thats the only msg it saw"
        );

        let proto_b5 = Block::new(None, sender0, txs.clone());
        // println!("\n3 {:?}", m3);
        // println!("\n4 {:?}", m4);
        let (m5, weights) = BlockMsg::from_msgs(
            proto_b5.get_sender(),
            vec![&m3, &m2],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b5),
        ).unwrap();
        // println!("\nm5 {:?}", m5);
        // println!("\nm5_estimate {:?}", Block::from(&m5));

        // println!();
        assert_eq!(
            m5.get_estimate(),
            &Block::new(Some(Block::from(&m3)), sender0, txs.clone()),
            "should build on top of "
        );

        let mut block = Block::from(&m3);
        assert_eq!(
            block,
            Block::new(Some(Block::from(&m2)), sender3, txs.clone()),
        );
        // assert_eq!(block.get_prevblock(), Some(genesis_block),);
    }

    #[test]
    fn test2() {
        let (senderg, sender0, sender1, sender2, sender3, sender4, sender5) =
            (0, 1, 2, 3, 4, 5, 6); // miner identities
        let (weightg, weight0, weight1, weight2, weight3, weight4, weight5) =
            (1.0, 1.0, 1.0, 1.0, 1.0, 1.1, 1.0); // and their corresponding weights
        let senders_weights = SendersWeight::new(
            [
                (senderg, weightg),
                (sender0, weight0),
                (sender1, weight1),
                (sender2, weight2),
                (sender3, weight3),
                (sender4, weight4),
                (sender5, weight5),
            ].iter()
                .cloned()
                .collect(),
        );
        let weights = SenderState::new(
            senders_weights.clone(),
            0.0,            // state fault weight
            1.0,            // subjective fault weight threshold
            HashSet::new(), // equivocators
        );

        let txs = BTreeSet::new();

        // block dag
        let genesis_block = Block::from(ProtoBlock {
            prevblock: None,
            sender: senderg,
            txs: txs.clone(),
        });
        let justification = Justification::new();
        let genesis_block_msg =
            BlockMsg::new(senderg, justification, genesis_block.clone());
        // assert_eq!(
        //     &Block::from(&genesis_block_msg),
        //     &genesis_block,
        //     "genesis block with None as prevblock"
        // );
        let proto_b0 = Block::new(None, sender0, txs.clone());
        let (m0, weights) = BlockMsg::from_msgs(
            proto_b0.get_sender(),
            vec![&genesis_block_msg],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b0), // data
        ).unwrap();
        let proto_b1 = Block::new(None, sender1, txs.clone());
        let (m1, weights) = BlockMsg::from_msgs(
            proto_b1.get_sender(),
            vec![&m0],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b1),
        ).unwrap();
        let proto_b2 = Block::new(None, sender2, txs.clone());
        let (m2, weights) = BlockMsg::from_msgs(
            proto_b2.get_sender(),
            vec![&genesis_block_msg],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b2),
        ).unwrap();

        // assert_eq!(
        //     m2.get_estimate(),
        //     &Block::new(Some(Block::from(&m1)), sender2, txs.clone()),
        //     "should build on top of m1 as sender1 has more weight"
        // );

        let proto_b3 = Block::new(None, sender3, txs.clone());
        let (m3, weights) = BlockMsg::from_msgs(
            proto_b3.get_sender(),
            vec![&m2],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b3),
        ).unwrap();

        // assert_eq!(
        //     m3.get_estimate(),
        //     &Block::new(Some(Block::from(&m0)), sender3, txs.clone()),
        //     "should build on top of m0 as as thats the only msg it saw"
        // );

        let proto_b4 = Block::new(None, sender4, txs.clone());
        // println!("\n3 {:?}", m2);
        // println!("\n4 {:?}", m3);
        let (m4, weights) = BlockMsg::from_msgs(
            proto_b4.get_sender(),
            vec![&m2],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b4),
        ).unwrap();
        // assert_eq!(
        //     m4.get_estimate(),
        //     &Block::new(Some(Block::from(&m2)), sender4, txs.clone()),
        //     "should build on top of "
        // );

        let proto_b5 = Block::new(None, sender5, txs.clone());

        let (m5, weights) = BlockMsg::from_msgs(
            proto_b5.get_sender(),
            vec![&m0, &m1, &m2, &m3, &m4],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &weights,
            Some(proto_b5),
        ).unwrap();

        assert_eq!(
            m5.get_estimate(),
            &Block::new(Some(Block::from(&m4)), sender5, txs.clone()),
            "should build on top of "
        );
    }
}
