use std::collections::{HashSet};
use std::hash::{Hash};
use std::fmt::{Debug};

use traits::{Estimate};
use message::{Message, AbstractMsg};
use justification::{Justification, Weights};

type Miner = u32;
type BlockHash = u128;
type TxHash = u128;

trait Block: Send + Sync + Ord + Clone + Debug + Hash {}
impl Block for BlockHash {}

#[derive(Clone, Eq, Ord, PartialOrd, PartialEq, Hash, Default, Debug)]
struct BlockChain<B: Block> {
    prev_block: B,
}

impl BlockChain<BlockHash> {
    fn new(prev_block: BlockHash) -> Self {
        Self { prev_block }
    }
}

impl Estimate for BlockChain<BlockHash> {
    type M = Message<Self, Miner>;
    type Data = HashSet<Tx>;
    fn mk_estimate(
        justification: Vec<&Self::M>,
        weights: &Weights<Miner>,
        external_data: Option<Self::Data>, // mempool
    ) -> (Option<Self>, Justification<Self::M>, Weights<Miner>) {
        unimplemented!()
    }
}

struct Tx {
    tx_hash: TxHash,
}
