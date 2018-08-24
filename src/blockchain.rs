use std::collections::{BTreeSet, HashSet};
use traits::{Estimate, Data};
use message::{AbstractMsg, Message};
use justification::{Justification, Weights};
use senders_weight::{SendersWeight};
use std::convert::{From};
type Validator = u32;

/// a genesis block should be a block with estimate Block with prevblock =
/// None and data. data will be the unique identifier of this blockchain

#[derive(Clone, Default, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
pub struct Block {
    prevblock: Option<Box<Block>>,
    sender: Validator,
}

pub type BlockMsg = Message<Block /*Estimate*/, Validator /*Sender*/>;

#[derive(Clone, Eq, Debug, Ord, PartialOrd, PartialEq, Hash)]
pub struct Tx;

impl Data for Block {
    type Data = Self;
    fn is_valid(&self, _data: &Self::Data) -> bool {
        true // FIXME
    }
}

impl<'z> From<&'z BlockMsg> for Block {
    fn from(msg: &BlockMsg) -> Self {
        msg.get_estimate().clone()
    }
}

impl Block {
    pub fn new(prevblock: Option<Box<Block>>, sender: Validator) -> Self {
        Self { prevblock, sender }
    }
    pub fn from_prevblock_msg(
        prevblock_msg: Option<BlockMsg>,
        // a proto_block is a block with a None prevblock and is not a genesis_block
        proto_block: Block,
    ) -> Self {
        let prevblock = prevblock_msg.map(|m| Box::new(Block::from(&m)));
        Self { prevblock, ..proto_block }
    }
}

impl Estimate for Block {
    type M = BlockMsg;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        finalized_msg: Option<&Self::M>,
        weights: &Weights<<<Self as Estimate>::M as AbstractMsg>::Sender>,
        proto_block: Option<<Self as Data>::Data>,
    ) -> Self {
        match (latest_msgs.len(), proto_block) {
            (0, _) => panic!(
                "Needs at least one latest message to be able to pick one"
            ),
            (1, Some(proto_block)) => {
                let block = Self::from_prevblock_msg(
                    latest_msgs.iter().next().map(|msg| msg.clone()),
                    proto_block,
                );
                // TODO: here u have to verify that the proto_block is consistent with the block choice
                // is_valid_estimate
                block
            },
            (_, Some(proto_block)) => {
                let heaviest_msg = latest_msgs
                    .ghost(finalized_msg, weights.get_senders_weights());
                Self::from_prevblock_msg(heaviest_msg, proto_block)
            },
            (_, None) =>
                panic!("proto_block is None, and latest_msgs: {:?}", latest_msgs),
        }
    }
}

#[test]
fn example_usage() {
    let (sender0, sender1, sender2, sender3) = (0, 1, 2, 3); // miner identities
    let (weight0, weight1, weight2, weight3) = (1.0, 1.0, 2.0, 1.0); // and their corresponding weights
    let senders_weights = SendersWeight::new(
        [
            (sender0, weight0),
            (sender1, weight1),
            (sender2, weight2),
            (sender3, weight3),
        ].iter()
            .cloned()
            .collect(),
    );
    let weights = Weights::new(
        senders_weights.clone(),
        0.0,            // state fault weight
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    let estimate = Block {
        prevblock: None,
        sender: sender0,
    };
    let justification = Justification::new();
    let genesis_block_msg =
        BlockMsg::new(sender0, justification, estimate.clone());
    assert_eq!(
        genesis_block_msg.get_estimate(),
        &estimate,
        "genesis block with None as prevblock"
    );
    let proto_b1 = Block::new(None, sender1);
    let (m1, weights) = BlockMsg::from_msgs(
        proto_b1.sender,
        vec![&genesis_block_msg],
        None, // finalized_msg, could be genesis_block_msg
        &weights,
        Some(proto_b1), // data
    );
    let proto_b2 =  Block::new(None, sender2);
    let (m2, weights) = BlockMsg::from_msgs(
        proto_b2.sender,
        vec![&genesis_block_msg],
        None,
        &weights,
        Some(proto_b2),
    );
    let proto_b3 = Block::new(None, sender3);
    let (m3, weights) = BlockMsg::from_msgs(
        proto_b3.sender,
        vec![&m1, &m2],
        None,
        &weights,
        Some(proto_b3),
    );

    assert_eq!(
        m3.get_estimate(),
        &Block::new(Some(Box::new(Block::from(&m2))), sender3),
        "should build on top of m2 as sender2 has more weight"
    );
}
