use std::collections::{BTreeSet, HashMap, HashSet};
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
    height: u32,
    sender: Validator,
    txs: BTreeSet<Tx>,
}

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
pub struct Block(Arc<ProtoBlock>);

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
        Block(Arc::new(protoblock))
    }
}

// impl<'z> From<&'z BlockMsg> for Block {
//     fn from(msg: &BlockMsg) -> Self {
//         let estimate = msg.get_estimate();
//         Block::new(
//             Some(estimate.clone()),
//             msg.get_sender().clone(),
//             estimate.get_txs().clone(),
//         )
//     }
// }
impl<'z> From<&'z BlockMsg> for Block {
    fn from(msg: &BlockMsg) -> Self {
        msg.get_estimate().clone()
    }
}
// impl<'z> From<&'z BlockMsg> for Block {
//     fn from(msg: &BlockMsg) -> Self {
//         let estimate = msg.get_estimate();
//         Block::new(
//             Some(estimate.clone()),
//             msg.get_sender().clone(),
//             estimate.get_txs().clone(),
//         )
//     }
// }

impl Iterator for Block {
    type Item = Self;
    fn next(&mut self) -> Option<Self::Item> {
        self.get_prevblock()
    }
}

impl Block {
    pub fn new(
        prevblock: Option<Block>,
        sender: Validator,
        txs: BTreeSet<Tx>,
    ) -> Self {
        Block::from(ProtoBlock {
            height: Block::next_height(&prevblock),
            prevblock,
            sender,
            txs,
        })
    }

    pub fn next_height(block: &Option<Self>) -> u32 {
        match block {
            None => 0,
            Some(b) => b.get_height() + 1,
        }
    }
    pub fn get_txs(&self) -> &BTreeSet<Tx> {
        &self.0.txs
    }

    pub fn get_height(&self) -> &u32 {
        &self.0.height
    }
    pub fn get_sender(&self) -> Validator {
        self.0.sender
    }
    pub fn from_prevblock_msg(
        prevblock_msg: Option<BlockMsg>,
        // a preblock is a block with a None prevblock (ie, Estimate) AND is
        // not a genesis_block
        preblock: Block,
    ) -> Self {
        let prevblock = prevblock_msg.map(|m| Block::from(&m));
        let block = Block::from(ProtoBlock {
            height: Block::next_height(&prevblock),
            prevblock,
            ..(*preblock.0).clone()
        });

        if Block::is_valid(&block) {
            block
        }
        else {
            panic!("Block not valid")
        }
    }

    pub fn get_prevblock(&self) -> Option<Self> {
        self.0
            .prevblock
            .as_ref()
            .map(|prevblock| (*prevblock).clone())
    }
    // /// works without block height, but expensive
    // pub fn is_member(&self, rhs: &Self) -> bool {
    //     self == rhs
    //         || rhs
    //         .get_prevblock()
    //         .as_ref()
    //         .map(|prevblock| self.is_member(prevblock))
    //         .unwrap_or(false)
    // }

    /// works only with block height, but cheap
    pub fn is_member(&self, rhs: &Self) -> bool {
        match (self.get_height(), rhs.get_height()) {
            (l, r) if l > r => false,
            (l, r) if l < r => rhs
                .get_prevblock()
                .as_ref()
                .map(|prevblock| self.is_member(prevblock))
                .unwrap_or(false),
            _ => self == rhs,
        }
    }

    pub fn score(
        &self,
        latest_msg: &HashMap<
            <<Self as Estimate>::M as CasperMsg>::Sender,
            BlockMsg,
        >,
        senders_weights: &SendersWeight<
            <<Self as Estimate>::M as CasperMsg>::Sender,
        >,
    ) -> WeightUnit {
        let mut referred_senders = HashSet::new();
        latest_msg.iter().fold(WeightUnit::ZERO, |acc, (_, msg)| {
            let sender = msg.get_sender();
            if self.is_member(&Block::from(msg))
                && referred_senders.insert(sender)
            {
                acc + senders_weights
                    .get_weight(sender)
                    .unwrap_or(WeightUnit::ZERO)
            }
            else {
                acc
            }
        })
    }

    pub fn get_prefork_block(
        &self,
        rhs: &Self,
        mut validators: HashSet<Validator>,
    ) -> Option<(Block, HashSet<Validator>)> {
        let comp = self.get_height().cmp(rhs.get_height());
        match comp {
            Greater => self.get_prevblock().and_then(|b| {
                let _ = validators.insert(b.get_sender());
                b.get_prefork_block(rhs, validators)
            }),
            Equal =>
                if self == rhs {
                    // this is the prefork block
                    Some((self.clone(), validators))
                }
                else {
                    self.get_prevblock().and_then(|l| {
                        rhs.get_prevblock().and_then(|r| {
                            let _ = validators.insert(l.get_sender());
                            let _ = validators.insert(r.get_sender());
                            l.get_prefork_block(&r, validators)
                        })
                    })
                },
            Less => rhs.get_prevblock().and_then(|b| {
                let _ = validators.insert(b.get_sender());
                b.get_prefork_block(self, validators)
            }),
        }
    }

    pub fn descend(
        &self,
        height: &u32,
        mut validators: HashSet<Validator>,
        original_msg: Self,
    ) -> Option<(Block, HashSet<Validator>, Self)> {
        match height.cmp(self.get_height()) {
            Greater => {
                let _ = validators.insert(self.get_sender());
                self.get_prevblock()
                    .and_then(|b| b.descend(height, validators, original_msg))
            },
            Equal => Some((self.clone(), validators, original_msg)),
            Less => None,
        }
    }
    // pub fn branch_validators(
    //     justification: &Justification<BlockMsg>,
    //     senders_weights: &SendersWeight<<BlockMsg as CasperMsg>::Sender>,
    // ) -> HashMap<Block, (HashSet<Validator>, HashSet<Block>)> {

    // }

    // pub fn ghost(
    //     justification: &Justification<BlockMsg>,
    //     finalized_msg: Option<&BlockMsg>,
    //     senders_weights: &SendersWeight<<BlockMsg as CasperMsg>::Sender>,
    // ) -> Option<Block> {
    //     // fn recursor(msgs: VecDeque<BlockMsg>) -> Box<Iterator<Item = BlockMsg>> {}
    //     let mut latest_blocks: Vec<_> =
    //         justification.iter().map(|m| Block::from(m)).collect();
    //     // sort blocks by height
    //     latest_blocks
    //         .sort_unstable_by(|l, r| l.get_height().cmp(r.get_height()));
    //     let heights: Vec<_> =
    //         latest_blocks.iter().map(|b| b.get_height()).collect();
    //     let h_len = heights.len();
    //     // let min_height = if h_len > 0 {
    //     //     heights.iter().min().clone().unwrap()
    //     // }
    //     // else {
    //     //     return None;
    //     // };

    //     let i = 0;
    //     // blocks at the same height
    //     let aligned_bs: Vec<_> = latest_blocks
    //         .iter()
    //         .map(|block| {
    //             if h_len < i + 1 {
    //                 block.descend(heights[i + 1], HashSet::new(), block.clone())
    //             }
    //             else {
    //                 None
    //             }
    //         })
    //         .collect();

    //     aligned_bs.iter().fold(
    //         HashMap::new(),
    //         |acc: HashMap<Block, (HashSet<Validator>, HashSet<Block>)>,
    //          &Some((b, v, o))| {
    //             match acc.get_mut(&b) {
    //                 // fork found
    //                 Some((v_prime, o_prime)) => {
    //                     *v_prime = v_prime.union(&v).cloned().collect();
    //                     let _ = o_prime.insert(o);
    //                     acc
    //                 },
    //                 // no fork
    //                 None => {
    //                     let os = HashSet::new();
    //                     os.insert(o);
    //                     acc.insert(b, (v, os));
    //                     acc
    //                 },
    //             }
    //         },
    //     );

    //     // aligned_bs.fold(HashSet::new(), |acc, b| {
    //     //     acc.
    //     // });

    //     None
    // }

    /// nicos version
    pub fn ghost(
        justification: &Justification<BlockMsg>,
        finalized_msg: Option<&BlockMsg>,
        senders_weights: &SendersWeight<<BlockMsg as CasperMsg>::Sender>,
    ) -> Option<BlockMsg> {
        let mut latest_message_per_validator: HashMap<
            <<Self as Estimate>::M as CasperMsg>::Sender,
            BlockMsg,
        > = HashMap::new();

        // compute the last message for each validator
        for validator in senders_weights.get_senders().expect("err1") {
            let mut latest_messages: Vec<_> = justification
                .iter()
                .filter(|m| m.get_sender() == &validator)
                .collect();

            if latest_messages.len() > 0 {
                latest_messages.sort_unstable_by(|a, b| b.cmp(&a));
                latest_message_per_validator
                    .insert(validator, latest_messages[0].clone());
            }
        }

        let mut b = finalized_msg.unwrap(); // TODO figure out genesis block if None

        // GHOST
        loop {
            // get the id of the current block
            let b_cmp = b;
            println!("b: {:?}", Block::from(b));

            // get all children of b
            let b_children = latest_message_per_validator.iter().filter(|&(_, m)| {
                Block::from(m)
                    .get_prevblock()
                    .map(|block| {
                        // Block::from(b_cmp).is_member(&block)
                        Block::from(b_cmp) == block
                    })
                    .unwrap_or(false)
            });
            // println!("b: {:?}", b);
            // println!("b_children: {:?}", b_children);
            // get the score of each child
            let mut sorted_by_score_and_hash: Vec<_> = b_children
                .map(|(_, child)| {
                    (
                        child,
                        Block::from(child).score(
                            &latest_message_per_validator,
                            senders_weights,
                        ),
                    )
                })
                .collect();

            // sort by score (and hash TODO if max score is not unique)
            sorted_by_score_and_hash.sort_unstable_by(
                |(block, score), (block_prime, score_prime)| {
                    // sort by bigger score. and then by smaller hash value (here we consider id is the
                    // hash of the message)
                    score_prime
                        .partial_cmp(&score)
                        .unwrap_or(block.cmp(&block_prime))
                },
            );
            // if we have a next block, loop again
            if sorted_by_score_and_hash.len() > 0 {
                let (best_child, _) = sorted_by_score_and_hash[0];
                b = best_child;
            }
            // no next block, we have our complete blockchain
            else {
                break;
            }
        }

        Some(b.clone())
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
        // in fact i could put the whole mempool inside of this preblock and
        // search for a reasonable set of txs in this function that does not
        // conflict with the past blocks
        preblock: Option<<Self as Data>::Data>,
    ) -> Self {
        match (latest_msgs.len(), preblock) {
            (0, _) => panic!(
                "Needs at least one latest message to be able to pick one"
            ),
            (_, None) => panic!("preblock is None"),
            (1, Some(preblock)) => {
                // only msg to built on top, no choice thus no ghost
                let msg = latest_msgs.iter().next().map(|msg| msg.clone());
                Self::from_prevblock_msg(msg, preblock)
            },
            (_, Some(preblock)) => {
                let heaviest_msg =
                    Block::ghost(latest_msgs, finalized_msg, senders_weights);
                Self::from_prevblock_msg(heaviest_msg, preblock)
            },
        }
    }
}

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
        height: 0,
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

    assert!(Block::from(&m1).is_member(&Block::from(&m1)));
    assert!(!Block::from(&m1).is_member(&Block::from(&m2)));
    assert!(!Block::from(&m2).is_member(&Block::from(&m1)));
    assert!(!Block::from(&m1).is_member(&Block::from(&m2)));
    assert!(Block::from(&m2).is_member(&Block::from(&m3)));
    assert!(!Block::from(&m3).is_member(&Block::from(&m2)));
    assert!(!Block::from(&m3).is_member(&Block::from(&m1)));

    // let mut block = Block::from(&m3);
    // assert_eq!(
    //     block,
    //     Block::new(Some(Block::from(&m2)), sender3, txs.clone()),
    // );
    // assert_eq!(block.next(), Some(genesis_block),);
}
