use std::collections::{BTreeSet, HashSet};
use traits::{Estimate, Data};
use message::{AbstractMsg, Message};
use justification::{Justification, Weights};
use senders_weight::{SendersWeight};
type Miner = u32;

#[derive(Clone, Default, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
pub struct Blockchain {
    prev_block: Block,
    data: Option<<Block as AbstractMsg>::Data>,
}

impl Blockchain {
    pub fn new(
        prev_block: Block,
        data: Option<<Block as AbstractMsg>::Data>,
    ) -> Self {
        Blockchain { prev_block, data }
    }
}

pub type Block = Message<
    Blockchain, /*estimate*/
    Miner,      /*sender*/
    Txs,        /*data*/
>;

// TODO: i think its possible to do ghost in arbitrary data, that is default implementation
impl Estimate for Blockchain {
    type M = Block;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        finalized_msg: Option<&Self::M>,
        weights: &Weights<Miner>,
        data: Option<<<Self as Estimate>::M as AbstractMsg>::Data>,
    ) -> Option<Self> {
        let senders_weights = weights.get_senders_weights();
        latest_msgs
            .get_children_weights(finalized_msg, senders_weights)
            .iter()
            .max_by(|(_, &weight0), (_, &weight1)| {
                weight0
                    .partial_cmp(&weight1)
                    // tie breaker, the unwrap fails because both values are the
                    // same and we arbitrarily chose a result. TODO this should be
                    // something deterministic, like blockhash
                    .unwrap_or(::std::cmp::Ordering::Greater)
            })
            .and_then(|(prev_block, _)| {
                Some(Blockchain {
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

    let prev_block = None;
    let justification = Justification::new();
    let genesis_block = Block::new(sender0, justification, prev_block.clone());
    assert_eq!(
        genesis_block.get_estimate(),
        &prev_block,
        "genesis block with None as prev_block"
    );

    let (b1, weights) = Block::from_msgs(
        sender1,
        vec![&genesis_block],
        None, // finalized_msg, could be genesis_block
        &weights,
        None, // data
    );

    let (b2, weights) =
        Block::from_msgs(sender2, vec![&genesis_block], None, &weights, None);

    let (b3, weights) =
        Block::from_msgs(sender3, vec![&b1, &b2], None, &weights, None);

    // println!("estimate: {:?}", b3.get_estimate());

    assert_eq!(
        b3.get_estimate(),
        &Some(Blockchain {
            prev_block: b2,
            data: None,
        }),
        "should build on top of b2"
    )
}
