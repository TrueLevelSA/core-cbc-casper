use std::convert::{From};
use std::collections::{BTreeSet, HashSet};

use traits::{Estimate, Data, Zero};
use message::{CasperMsg, Message};
use justification::{Justification, SenderState};
use senders_weight::{SendersWeight};
use std::sync::Arc;
use weight_unit::{WeightUnit};
type Validator = u32;

/// a genesis block should be a block with estimate Block with prevblock =
/// None and data. data will be the unique identifier of this blockchain

#[derive(Clone, Default, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
pub struct Block {
    prevblock: Option<Arc<Block>>,
    sender: Validator,
    txs: BTreeSet<Tx>,
}

pub type BlockMsg = Message<Block /*Estimate*/, Validator /*Sender*/>;

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash)]
pub struct Tx;

impl Data for Block {
    type Data = Self;
    fn is_valid(_data: &Self::Data) -> bool {
        true // FIXME
    }
}

impl<'z> From<&'z BlockMsg> for Block {
    fn from(msg: &BlockMsg) -> Self {
        msg.get_estimate().clone()
    }
}

impl Block {
    pub fn new(
        prevblock: Option<Arc<Block>>,
        sender: Validator,
        txs: BTreeSet<Tx>,
    ) -> Self {
        Self {
            prevblock,
            sender,
            txs,
        }
    }
    pub fn from_prevblock_msg(
        prevblock_msg: Option<BlockMsg>,
        // a proto_block is a block with a None prevblock (ie, Estimate) AND is
        // not a genesis_block
        proto_block: Block,
    ) -> Self {
        let prevblock = prevblock_msg.map(|m| Arc::new(Block::from(&m)));
        let block = Self {
            prevblock,
            ..proto_block
        };

        if Block::is_valid(&block) {
            block
        }
        else {
            panic!("Block not valid")
        }
    }

    pub fn get_prevblock(&self) -> Option<Self> {
        self.prevblock
            .as_ref()
            .map(|prevblock| (**prevblock).clone())
    }

    pub fn is_member(&self, rhs: &Self) -> bool {
        self == rhs
            || rhs
                .get_prevblock()
                .as_ref()
                .map(|prevblock| self.is_member(prevblock))
                .unwrap_or(false)
    }

    pub fn score(
        &self,
        latest_msg: Justification<BlockMsg>,
        senders_weights: &SendersWeight<
            <<Self as Estimate>::M as CasperMsg>::Sender,
        >,
    ) -> WeightUnit {
        latest_msg.iter().fold(WeightUnit::ZERO, |acc, msg| {
            if self.is_member(&Block::from(msg)) {
                acc + senders_weights
                    .get_weight(msg.get_sender())
                    .unwrap_or(WeightUnit::ZERO)
            }
            else {
                acc
            }
        })
    }

    // pub fn children()
}

impl Estimate for Block {
    type M = BlockMsg;
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
        match (latest_msgs.len(), proto_block) {
            (0, _) => panic!(
                "Needs at least one latest message to be able to pick one"
            ),
            (_, None) => panic!("proto_block is None"),
            (1, Some(proto_block)) => {
                // only msg to built on top, no choice thus no ghost
                let msg = latest_msgs.iter().next().map(|msg| msg.clone());
                Self::from_prevblock_msg(msg, proto_block)
            },
            (_, Some(proto_block)) => {
                let heaviest_msg =
                    latest_msgs.ghost(finalized_msg, senders_weights);
                Self::from_prevblock_msg(heaviest_msg, proto_block)
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
    // (s0, w=1)   gen
    // (s1, w=1)    |\--m1---\
    // (s2, w=2)    \---m2--\|
    // (s3, w=1)         \---m3

    // blockchain gen <--m2 <--m3
    let genesis_block = Block {
        prevblock: None,
        sender: sender0,
        txs: txs.clone(),
    };
    let justification = Justification::new();
    let genesis_block_msg =
        BlockMsg::new(sender0, justification, genesis_block.clone());
    assert_eq!(
        genesis_block_msg.get_estimate(),
        &genesis_block,
        "genesis block with None as prevblock"
    );
    let proto_b1 = Block::new(None, sender1, txs.clone());
    let (m1, weights) = BlockMsg::from_msgs(
        proto_b1.sender,
        vec![&genesis_block_msg],
        None, // finalized_msg, could be genesis_block_msg
        &weights,
        Some(proto_b1), // data
    ).unwrap();
    let proto_b2 = Block::new(None, sender2, txs.clone());
    let (m2, weights) = BlockMsg::from_msgs(
        proto_b2.sender,
        vec![&genesis_block_msg],
        None,
        &weights,
        Some(proto_b2),
    ).unwrap();
    let proto_b3 = Block::new(None, sender3, txs.clone());
    let (m3, weights) = BlockMsg::from_msgs(
        proto_b3.sender,
        vec![&m1, &m2],
        None,
        &weights,
        Some(proto_b3),
    ).unwrap();

    assert_eq!(
        m3.get_estimate(),
        &Block::new(Some(Arc::new(Block::from(&m2))), sender3, txs.clone()),
        "should build on top of m2 as sender2 has more weight"
    );

    let proto_b4 = Block::new(None, sender4, txs.clone());
    let (m4, weights) = BlockMsg::from_msgs(
        proto_b4.sender,
        vec![&m1],
        None,
        &weights,
        Some(proto_b4),
    ).unwrap();

    assert_eq!(
        m4.get_estimate(),
        &Block::new(Some(Arc::new(Block::from(&m1))), sender4, txs.clone()),
        "should build on top of m1 as as thats the only msg it saw"
    );

    // let proto_b5 = Block::new(None, sender0, txs.clone());
    // let (m5, weights) = BlockMsg::from_msgs(
    //     proto_b5.sender,
    //     vec![&m3, &m4],
    //     None,
    //     &weights,
    //     Some(proto_b5),
    // ).unwrap();

    // assert_eq!(
    //     m5.get_estimate(),
    //     &Block::new(Some(Box::new(Block::from(&m4))), sender0, txs.clone()),
    //     "should build on top of "
    // );
    assert!(Block::from(&m1).is_member(&Block::from(&m1)));
    assert!(!Block::from(&m1).is_member(&Block::from(&m2)));
    assert!(!Block::from(&m2).is_member(&Block::from(&m1)));
    assert!(!Block::from(&m1).is_member(&Block::from(&m2)));
    assert!(Block::from(&m2).is_member(&Block::from(&m3)));
    assert!(!Block::from(&m3).is_member(&Block::from(&m2)));
    assert!(!Block::from(&m3).is_member(&Block::from(&m1)));
}
