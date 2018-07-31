use std::collections::{HashSet};
use std::hash::{Hash};
use std::fmt::{Debug};

use traits::{Estimate, Data, Sender};
use message::{AbstractMsg, Message};
use justification::{Justification, Weights};
use senders_weight::{SendersWeight};

type Miner = u32;
type TxHash = u128;
type BlockHash = u128;
type Block = Message<BlockHash /*estimate*/, Miner /*sender*/>;

impl Estimate for BlockHash {
    type M = Block;
    type Sender = Miner;
    type Data = Txs;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        weights: &Weights<Miner>,
        external_data: Option<Self::Data>, // mempool
    ) -> Option<Self> {
        unimplemented!()
    }
}

// impl Block{
//     fn score<'a>(
//         block: Block,
//         validators_weights: &HashMap<Validator, Weight>,
//         latest_message_per_validator: &HashMap<Validator, &Message>,
//     ) -> f64 {
//         let mut score: f64 = 0.0;

//         // for each validator, check if the last message is in the blockchain of "block"
//         // if it's the case, add the weight of the validator to the score
//         for (validator, last_message) in latest_message_per_validator.iter() {
//             let mut current_message: Option<&Message> = Some(last_message);
//             loop {
//                 match current_message {
//                     Some(m) => {
//                         if m.id == block.id {
//                             score += validators_weights.get(validator).unwrap();
//                             // current block is reached, break loop
//                             break;
//                         }
//                         else {
//                             current_message = m.estimate;
//                         }
//                     },
//                     // genesis block is reached, break loop
//                     None => break,
//                 }
//             }
//         }

//         score
//     }
// }

#[derive(Eq, Ord, PartialOrd, PartialEq, Clone, Default, Hash, Debug)]
pub struct Tx {
    tx_hash: TxHash,
}

pub type Txs = HashSet<Tx>;
impl Data for Txs {}

#[test]
fn blockchain() {
    let miner = 10;
    let prev_blockhash = Some(12903129019213819310839128);
    let justification = Justification::new();
    let genesis_block = Block::new(miner, justification, prev_blockhash);
    assert_eq!(genesis_block.get_estimate(), prev_blockhash, "hardcoded");
}
