use std::collections::{HashSet};
use std::hash::{Hash};
use std::fmt::{Debug};

use traits::{Estimate, Data};
use message::{AbstractMsg};
use justification::{Justification, Weights};

type Miner = u32;
type TxHash = u128;

#[derive(Eq, Ord, PartialOrd, PartialEq, Clone, Default, Hash, Debug)]
struct Block {
    sender: Miner,
    prev_block: Justification<Block>,
}

impl Block {}

impl AbstractMsg for Block {
    type Estimate = Self;
    type Sender = Miner;
    fn get_sender(&self) -> Self::Sender {
        self.sender
    }
    fn get_justification<'z>(&'z self) -> &'z Justification<Self> {
        &self.prev_block
    }
    fn get_estimate(&self) -> Option<Self> {
        Some(self.clone())
    }
    fn new(
        sender: Self::Sender,
        justification: Justification<Self>,
        _estimate: Option<Self::Estimate>,
    ) -> Self {
        assert!(
            justification.len() == 1,
            "a prev_block on a blockchain must have a length = 1"
        );
        Block {
            sender,
            prev_block: justification,
        }
    }
}

impl Estimate for Block {
    type M = Self;
    // type Data = Txs;
    type Sender = Miner;
    fn mk_estimate<D: Data>(
        latest_msgs: Vec<&Self::M>,
        weights: &Weights<Miner>,
        external_data: Option<D>, // mempool
    ) -> (Option<Self>, Justification<Self::M>, Weights<Miner>) {
        unimplemented!()
    }
}

#[derive(Eq, Ord, PartialOrd, PartialEq, Clone, Default, Hash, Debug)]
struct Tx {
    tx_hash: TxHash,
}

type Txs = HashSet<Tx>;

impl Data for Txs{}

