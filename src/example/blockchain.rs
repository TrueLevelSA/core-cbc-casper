use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::convert::From;
use std::iter::{Iterator};

use justification::{Justification, LatestMsgsHonest, LatestMsgs};
use message::{CasperMsg, Message};
use senders_weight::SendersWeight;
use std::sync::Arc;
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

/// Boxing of a block, will be implemented as a CasperMsg
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

    /// Create a new block from a prevblock message and an incomplete block 
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
        } else {
            Err("Block not valid")
        }
    }

    /// Math definition of blockchain membership
    pub fn is_member(&self, rhs: &Self) -> bool {
        self == rhs
            || rhs
                .get_prevblock()
                .as_ref()
                .map(|prevblock| self.is_member(prevblock))
                .unwrap_or(false)
    }

    pub fn safety_oracles(
        block: Block,
        latest_msgs_honest: &LatestMsgsHonest<BlockMsg>,
        equivocators: &HashSet<<BlockMsg as CasperMsg>::Sender>,
        safety_oracle_threshold: WeightUnit,
        weights: &SendersWeight<Validator>,
    ) -> HashSet<BTreeSet<<BlockMsg as CasperMsg>::Sender>> {

        fn latest_in_justification(
            j: &Justification<BlockMsg>,
            equivocators: &HashSet<<BlockMsg as CasperMsg>::Sender>,
        ) -> HashMap<<BlockMsg as CasperMsg>::Sender, BlockMsg> {
            LatestMsgsHonest::from_latest_msgs(
                &LatestMsgs::from(j),
                equivocators,
            ).iter()
                .map(|m| (m.get_sender().clone(), m.clone()))
                .collect()
        }

        let latest_containing_block: HashSet<&BlockMsg> = latest_msgs_honest
            .iter()
            .filter(|&msg| block.is_member(&Block::from(msg)))
            .collect();

        let latest_agreeing_in_sender_view: HashMap<
            <BlockMsg as CasperMsg>::Sender,
            HashMap<<BlockMsg as CasperMsg>::Sender, BlockMsg>,
        > = latest_containing_block
            .iter()
            .map(|m| {
                (
                    m.get_sender().clone(),
                    latest_in_justification(
                        m.get_justification(),
                        equivocators,
                    ).into_iter()
                        .filter(|(_sender, msg)| {
                            block.is_member(&Block::from(msg))
                        })
                        .collect(),
                )
            })
            .collect();

        let neighbours: HashMap<
            &<BlockMsg as CasperMsg>::Sender,
            HashSet<&<BlockMsg as CasperMsg>::Sender>,
        > = latest_agreeing_in_sender_view
            .iter()
            .map(|(sender, seen_agreeing)| {
                (
                    sender,
                    seen_agreeing
                        .keys()
                        .filter(|senderb| {
                            latest_agreeing_in_sender_view[senderb]
                                .contains_key(&sender.clone())
                        })
                        .collect(),
                )
            })
            .collect();
        // println!("neighbours: {:?}", neighbours);
        fn bron_kerbosch(
            r: HashSet<&<BlockMsg as CasperMsg>::Sender>,
            p: HashSet<&<BlockMsg as CasperMsg>::Sender>,
            x: HashSet<&<BlockMsg as CasperMsg>::Sender>,
            mx_clqs: &mut HashSet<BTreeSet<<BlockMsg as CasperMsg>::Sender>>,
            neighbours: HashMap<
                &<BlockMsg as CasperMsg>::Sender,
                HashSet<&<BlockMsg as CasperMsg>::Sender>,
            >,
        ) {
            // println!("recursed");
            if p.is_empty() && x.is_empty() {
                let rnew: BTreeSet<
                    <BlockMsg as CasperMsg>::Sender,
                > = r.into_iter().map(|x| x.clone()).collect();
                mx_clqs.insert(rnew);
            } else {
                let piter = p.clone();
                let mut p = p;
                let mut x = x;
                piter.into_iter().for_each(|i| {
                    p.remove(i);
                    let mut rnew = r.clone();
                    rnew.insert(i);
                    let pnew: HashSet<
                        &<BlockMsg as CasperMsg>::Sender,
                    > = p.intersection(&neighbours[i]).cloned().collect();
                    let xnew: HashSet<
                        &<BlockMsg as CasperMsg>::Sender,
                    > = x.intersection(&neighbours[i]).cloned().collect();
                    x.insert(i);
                    bron_kerbosch(rnew, pnew, xnew, mx_clqs, neighbours.clone())
                })
            }
        }

        let p = neighbours.iter().fold(HashSet::new(), |acc, (_sender, x)| {
            acc.union(x).cloned().collect()
        });

        let mut mx_clqs = HashSet::new();

        bron_kerbosch(
            HashSet::new(),
            p,
            HashSet::new(),
            &mut mx_clqs,
            neighbours,
        );

        mx_clqs
            .into_iter()
            .filter(|x| {
                x.iter().fold(WeightUnit::ZERO, |acc, sender| {
                    acc + weights.get_weight(sender).unwrap_or(::std::f64::NAN)
                }) > safety_oracle_threshold
            })
            .collect()
    }
    // pub fn safety_oracle(
    //     latest_msgs_honest: &LatestMsgsHonest<BlockMsg>,
    //     validator: &<BlockMsg as CasperMsg>::Sender,
    //     equivocators: &HashSet<<BlockMsg as CasperMsg>::Sender>,
    //     all_honest_senders: &HashSet<<BlockMsg as CasperMsg>::Sender>,
    // ) -> bool {
    //     let (val_msgs, rest): (HashSet<_>, HashSet<_>) = latest_msgs_honest
    //         .iter()
    //         .partition(|&msg| msg.get_sender() == validator);
    //     let val_latests_msg: &BlockMsg = *val_msgs.iter().next().unwrap();
    //     let msg_for_prop = val_latests_msg
    //         .get_msg_for_proposition(all_honest_senders)
    //         .iter()
    //         .next()
    //         .cloned()
    //         .unwrap();
    //     let prop = Block::from(&msg_for_prop);
    //     rest.iter()
    //         .all(|&msg| prop.is_member(&Block::from(msg)))
    // }

    //TODO: this should possibly go to Estimate trait (not sure)
    pub fn set_as_final(&mut self) -> () {
        let mut proto_block = (**self.0).clone();
        proto_block.prevblock = None;
        *self.0 = Arc::new(proto_block);
    }

    pub fn get_prevblock(&self) -> Option<Self> {
        self.0.prevblock.as_ref().cloned()
    }

    /// parses blockchain using the latest honest messages
    /// the return value is a tuple containing a map and a set
    /// the hashmap maps blocks to their respective children
    /// the set contains all the blocks that have the genesis as their
    /// prevblock (aka all the children of the genesis block)
    pub fn parse_blockchains(
        latest_msgs: &LatestMsgsHonest<BlockMsg>,
        _finalized_msg: Option<&BlockMsg>,
    ) -> (HashMap<Block, HashSet<Block>>, HashSet<Block>) {

        // start at the tip of the blockchain
        let mut visited: HashMap<Block, HashSet<Block>> = latest_msgs
            .iter()
            .map(|msg| {
                let parent = Block::from(msg);
                let children = HashSet::new();
                (parent, children)
            })
            .collect();

        let mut queue: VecDeque<Block> = visited.keys().cloned().collect();
        let mut genesis: HashSet<Block> = HashSet::new();

        // while there is still unvisited blocks
        while let Some(child) = queue.pop_front() {
            match child.get_prevblock() {
                // if the prevblock is set, update the visited map
                Some(parent) => {
                    if visited.contains_key(&parent) {
                        // visited parent before, fork found
                        visited.get_mut(&parent).map(|parents_children| {
                            parents_children.insert(child);
                        });
                    } else {
                        // didnt visit parent before, set initial state, and push to queue
                        let mut parents_children = HashSet::new();
                        parents_children.insert(child);
                        visited.insert(parent.clone(), parents_children);
                        queue.push_back(parent);
                    }
                }
                // if not, update the genesis set, as a None prevblock indicates the genesis
                None => {
                    genesis.insert(child);
                }
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
                } else {
                    (b_block, b_weight, b_children)
                }
            })
        });
        heaviest_child.and_then(|(b_block, b_weight, b_children)| {
            if b_children.is_empty() {
                // base case
                Some((b_block, b_weight, b_children))
            } else {
                // recurse
                Self::pick_heaviest(&b_children, visited, &weights)
            }
        })
    }

    pub fn ghost(
        latest_msgs: &LatestMsgsHonest<BlockMsg>,
        finalized_msg: Option<&BlockMsg>,
        senders_weights: &SendersWeight<<BlockMsg as CasperMsg>::Sender>,
    ) -> Option<Self> {
        let (visited, genesis) =
            Self::parse_blockchains(latest_msgs, finalized_msg);
        Block::pick_heaviest(&genesis, &visited, senders_weights)
            .and_then(|(opt_block, ..)| opt_block)
    }
}

impl Estimate for Block {
    type M = BlockMsg;

    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
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
                let msg = latest_msgs.iter().next().cloned();
                Self::from_prevblock_msg(msg, incomplete_block).unwrap()
            }
            (_, Some(incomplete_block)) => {
                let prevblock =
                    Block::ghost(latest_msgs, finalized_msg, senders_weights);
                let block = Block::from(ProtoBlock {
                    prevblock,
                    ..(**incomplete_block.0).clone()
                });
                block
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::iter;
    use std::iter::{FromIterator};

    use super::*;
    use ::justification::{Justification, LatestMsgs, SenderState};

    #[test]
    fn example_usage() {
        let (sender0, sender1, sender2, sender3, sender4) = (0, 1, 2, 3, 4); // miner identities
        let (weight0, weight1, weight2, weight3, weight4) =
            (1.0, 1.0, 2.0, 1.0, 1.1); // and their corresponding sender_state
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
        let sender_state = SenderState::new(
            senders_weights.clone(),
            0.0, // state fault weight
            None,  // latest messages
            LatestMsgs::new(),
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
        let latest_msgs = Justification::new();
        let genesis_block_msg =
            BlockMsg::new(sender0, latest_msgs, genesis_block.clone());
        assert_eq!(
            &Block::from(&genesis_block_msg),
            &genesis_block,
            "genesis block with None as prevblock"
        );

        let proto_b1 = Block::new(None, sender1, txs.clone());
        let (m1, _) = BlockMsg::from_msgs(
            proto_b1.get_sender(),
            vec![&genesis_block_msg],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
            Some(proto_b1), // data
        ).unwrap();

        let proto_b2 = Block::new(None, sender2, txs.clone());
        let (m2, _) = BlockMsg::from_msgs(
            proto_b2.get_sender(),
            vec![&genesis_block_msg],
            None,
            &sender_state,
            Some(proto_b2),
        ).unwrap();

        let proto_b3 = Block::new(None, sender3, txs.clone());
        let (m3, _) = BlockMsg::from_msgs(
            proto_b3.get_sender(),
            vec![&m1, &m2],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
            Some(proto_b3),
        ).unwrap();

        assert_eq!(
            m3.get_estimate(),
            &Block::new(Some(Block::from(&m2)), sender3, txs.clone()),
            "should build on top of m2 as sender2 has more weight"
        );

        let proto_b4 = Block::new(None, sender4, txs.clone());
        let (m4, _) = BlockMsg::from_msgs(
            proto_b4.get_sender(),
            vec![&m1],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
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
        let (m5, _) = BlockMsg::from_msgs(
            proto_b5.get_sender(),
            vec![&m3, &m2],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
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

        let block = Block::from(&m3);
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
            (1.0, 1.0, 1.0, 1.0, 1.0, 1.1, 1.0); // and their corresponding sender_state

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

        let sender_state = SenderState::new(
            senders_weights.clone(),
            0.0, // state fault weight
            None,  // latest messages
            LatestMsgs::new(),
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
        let latest_msgs = Justification::new();
        let genesis_block_msg =
            BlockMsg::new(senderg, latest_msgs, genesis_block.clone());
        // assert_eq!(
        //     &Block::from(&genesis_block_msg),
        //     &genesis_block,
        //     "genesis block with None as prevblock"
        // );
        let proto_b0 = Block::new(None, sender0, txs.clone());
        let (m0, sender_state) = BlockMsg::from_msgs(
            proto_b0.get_sender(),
            vec![&genesis_block_msg],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
            Some(proto_b0), // data
        ).unwrap();

        let proto_b1 = Block::new(None, sender1, txs.clone());
        let (m1, sender_state) = BlockMsg::from_msgs(
            proto_b1.get_sender(),
            vec![&m0],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
            Some(proto_b1),
        ).unwrap();

        let proto_b2 = Block::new(None, sender2, txs.clone());
        let (m2, sender_state) = BlockMsg::from_msgs(
            proto_b2.get_sender(),
            vec![&genesis_block_msg],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
            Some(proto_b2),
        ).unwrap();

        // assert_eq!(
        //     m2.get_estimate(),
        //     &Block::new(Some(Block::from(&m1)), sender2, txs.clone()),
        //     "should build on top of m1 as sender1 has more weight"
        // );

        let proto_b3 = Block::new(None, sender3, txs.clone());
        let (m3, sender_state) = BlockMsg::from_msgs(
            proto_b3.get_sender(),
            vec![&m2],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
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
        let (m4, sender_state) = BlockMsg::from_msgs(
            proto_b4.get_sender(),
            vec![&m2],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
            Some(proto_b4),
        ).unwrap();
        // assert_eq!(
        //     m4.get_estimate(),
        //     &Block::new(Some(Block::from(&m2)), sender4, txs.clone()),
        //     "should build on top of "
        // );

        let proto_b5 = Block::new(None, sender5, txs.clone());

        let (m5, _) = BlockMsg::from_msgs(
            proto_b5.get_sender(),
            vec![&m0, &m1, &m2, &m3, &m4],
            Some(&genesis_block_msg), // finalized_msg, could be genesis_block_msg
            &sender_state,
            Some(proto_b5),
        ).unwrap();

        assert_eq!(
            m5.get_estimate(),
            &Block::new(Some(Block::from(&m4)), sender5, txs.clone()),
            "should build on top of "
        );
    }

    #[test]
    fn safety_oracles() {
        let nodes = 3;
        let senders: Vec<u32> = (0..nodes).collect();
        let weights: Vec<f64> =
            iter::repeat(1.0).take(nodes as usize).collect();

        let senders_weights = SendersWeight::new(
            senders
                .iter()
                .cloned()
                .zip(weights.iter().cloned())
                .collect(),
        );

        let sender_state = SenderState::new(
            senders_weights.clone(),
            0.0,  // state fault weight
            None, // latest messages
            LatestMsgs::new(),
            1.0,            // subjective fault weight threshold
            HashSet::new(), // equivocators
        );

        let txs = BTreeSet::new();

        // block dag
        let proto_b0 = Block::from(ProtoBlock {
            prevblock: None,
            sender: senders[0],
            txs: txs.clone(),
        });
        let latest_msgs = Justification::new();
        let m0 = BlockMsg::new(senders[0], latest_msgs, proto_b0.clone());

        let proto_b1 =
            Block::new(Some(proto_b0.clone()), senders[1], txs.clone());
        let (m1, sender_state) = BlockMsg::from_msgs(
            proto_b1.get_sender(),
            vec![&m0],
            None,
            &sender_state,
            Some(proto_b1.clone()),
        ).unwrap();

        let proto_b2 =
            Block::new(Some(proto_b1.clone()), senders[0], txs.clone());
        let (m2, sender_state) = BlockMsg::from_msgs(
            proto_b2.get_sender(),
            vec![&m1],
            None,
            &sender_state,
            Some(proto_b2.clone()),
        ).unwrap();

        // no clique yet, since senders[1] has not seen senders[0] seeing senders[1] having proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    sender_state.get_equivocators()
                ),
                sender_state.get_equivocators(),
                2.0,
                &senders_weights
            ),
            HashSet::new()
        );

        let proto_b3 =
            Block::new(Some(proto_b2.clone()), senders[1], txs.clone());
        let (m3, sender_state) = BlockMsg::from_msgs(
            proto_b3.get_sender(),
            vec![&m2],
            None,
            &sender_state,
            Some(proto_b3.clone()),
        ).unwrap();

        // clique, since both senders have seen each other having proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    sender_state.get_equivocators()
                ),
                sender_state.get_equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                senders[0], senders[1],
            ])])
        );

        let proto_b4 =
            Block::new(Some(proto_b3.clone()), senders[2], txs.clone());
        let (m4, sender_state) = BlockMsg::from_msgs(
            proto_b4.get_sender(),
            vec![&m3],
            None,
            &sender_state,
            Some(proto_b4.clone()),
        ).unwrap();

        let proto_b5 =
            Block::new(Some(proto_b4.clone()), senders[1], txs.clone());
        let (m5, sender_state) = BlockMsg::from_msgs(
            proto_b5.get_sender(),
            vec![&m4],
            None,
            &sender_state,
            Some(proto_b5.clone()),
        ).unwrap();

        // no second clique yet, since senders[2] has not seen senders[1] seeing senders[2] having proto_b0.clone() in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    sender_state.get_equivocators()
                ),
                sender_state.get_equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                senders[0], senders[1],
            ])])
        );

        let proto_b6 =
            Block::new(Some(proto_b5.clone()), senders[2], txs.clone());
        let (m6, sender_state) = BlockMsg::from_msgs(
            proto_b6.get_sender(),
            vec![&m5],
            None,
            &sender_state,
            Some(proto_b5.clone()),
        ).unwrap();

        // have two cliques on proto_b0 now
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    sender_state.get_equivocators()
                ),
                sender_state.get_equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![
                BTreeSet::from_iter(vec![senders[0], senders[1]]),
                BTreeSet::from_iter(vec![senders[1], senders[2]]),
            ])
        );
        // also have two cliques on proto_b1
        assert_eq!(
            Block::safety_oracles(
                proto_b1.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    sender_state.get_equivocators()
                ),
                sender_state.get_equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![
                BTreeSet::from_iter(vec![senders[0], senders[1]]),
                BTreeSet::from_iter(vec![senders[1], senders[2]]),
            ])
        );
        // on proto_b2, only have clique {1, 2}
        assert_eq!(
            Block::safety_oracles(
                proto_b2.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    sender_state.get_equivocators()
                ),
                sender_state.get_equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![
                BTreeSet::from_iter(vec![senders[1], senders[2]]),
            ])
        );

        let proto_b7 =
            Block::new(Some(proto_b6.clone()), senders[0], txs.clone());
        let (m7, sender_state) = BlockMsg::from_msgs(
            proto_b7.get_sender(),
            vec![&m6],
            None,
            &sender_state,
            Some(proto_b6.clone()),
        ).unwrap();

        let proto_b8 =
            Block::new(Some(proto_b7.clone()), senders[2], txs.clone());
        let (m8, sender_state) = BlockMsg::from_msgs(
            proto_b8.get_sender(),
            vec![&m7],
            None,
            &sender_state,
            Some(proto_b7.clone()),
        ).unwrap();

        let proto_b9 =
            Block::new(Some(proto_b8.clone()), senders[0], txs.clone());
        let (_, sender_state) = BlockMsg::from_msgs(
            proto_b9.get_sender(),
            vec![&m8],
            None,
            &sender_state,
            Some(proto_b8.clone()),
        ).unwrap();

        // now entire network is clique
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    sender_state.get_equivocators()
                ),
                sender_state.get_equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![
                BTreeSet::from_iter(vec![senders[0], senders[1], senders[2]]),
            ])
        );
        assert_eq!(
            Block::safety_oracles(
                proto_b2.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    sender_state.get_equivocators()
                ),
                sender_state.get_equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![
                BTreeSet::from_iter(vec![senders[0], senders[1], senders[2]]),
            ])
        );
    }
}
