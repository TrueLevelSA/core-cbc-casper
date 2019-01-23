use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::convert::From;
use std::iter::Iterator;

use hashed::Hashed;
use justification::{Justification, LatestMsgs, LatestMsgsHonest};
use message::{CasperMsg, Message};
use senders_weight::SendersWeight;
use serde_derive::Serialize;
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::{Arc, RwLock};
use traits::{Data, Estimate, Id, Sender, Zero};
use weight_unit::WeightUnit;

/// a genesis block should be a block with estimate Block with prevblock =
/// None and data. data will be the unique identifier of this blockchain
#[derive(Clone, Eq, PartialEq, Debug, Hash, Serialize)]
pub struct ProtoBlock<S: Sender> {
    prevblock: Option<Block<S>>,
    sender_type: PhantomData<S>,
}

impl<S: Sender> ProtoBlock<S> {
    pub fn new(prevblock: Option<Block<S>>) -> ProtoBlock<S> {
        ProtoBlock {
            prevblock,
            sender_type: PhantomData,
        }
    }
}

/// Boxing of a block, will be implemented as a CasperMsg
#[derive(Clone, Eq, Hash)]
pub struct Block<S: Sender>((Arc<ProtoBlock<S>>, Hashed));

impl<S: Sender> Default for Block<S> {
    fn default() -> Self {
        Block::new(None)
    }
}
// #[cfg(feature = "integration_test")]
// impl<S: Sender + Into<S>> From<S> for Block<S> {
//     fn from(sender: S) -> Self {
//         Block::from(ProtoBlock::new(None))
//     }
// }

// #[cfg(feature = "integration_test")]
// impl<S: Sender> std::fmt::Debug for Block<S> {
//     fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
//         match self.prevblock() {
//             None => write!(
//                 fmt,
//                 "{:?} -> {:?}",
//                 (self.sender(), self.id()),
//                 None::<Block<S>>
//             ),
//             Some(block) => write!(fmt, "{:?} -> {:?}", (self.sender(), self.id()), block),
//         }
//     }
// }

// #[cfg(not(feature = "integration_test"))]
impl<S: Sender> std::fmt::Debug for Block<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{:?} -> {:?}",
            self.id(),
            self.prevblock()
                .as_ref()
                .map(|p| p.id())
                .unwrap_or(&Hashed::default())
        )
    }
}

impl<S: Sender> serde::Serialize for Block<S> {
    fn serialize<T: serde::Serializer>(&self, rhs: T) -> Result<T::Ok, T::Error> {
        use serde::ser::SerializeStruct;
        let mut msg = rhs.serialize_struct("Block", 1)?;
        msg.serialize_field("prevblock", &self.prevblock())?;
        msg.end()
    }
}

impl<S: Sender> Id for ProtoBlock<S> {
    type ID = Hashed;
}

impl<S: Sender> Id for Block<S> {
    type ID = Hashed;
}

pub type BlockMsg<S> = Message<Block<S> /*Estimate*/, S /*Sender*/>;

impl<S: Sender> PartialEq for Block<S> {
    fn eq(&self, rhs: &Self) -> bool {
        Arc::ptr_eq(self.arc(), rhs.arc()) || self.id() == rhs.id()
    }
}

impl<S: Sender> From<ProtoBlock<S>> for Block<S> {
    fn from(protoblock: ProtoBlock<S>) -> Self {
        let id = protoblock.getid();
        Block((Arc::new(protoblock), id))
    }
}

impl<'z, S: Sender> From<&'z BlockMsg<S>> for Block<S> {
    fn from(msg: &BlockMsg<S>) -> Self {
        msg.estimate().clone()
    }
}

impl<S: Sender> Block<S> {
    pub fn new(prevblock: Option<Block<S>>) -> Self {
        Block::from(ProtoBlock::new(prevblock))
    }
    pub fn id(&self) -> &<Self as Id>::ID {
        &(self.0).1
    }
    fn arc(&self) -> &Arc<ProtoBlock<S>> {
        &(self.0).0
    }
    /// Create a new block from a prevblock message and an incomplete block
    pub fn from_prevblock_msg(
        prevblock_msg: Option<BlockMsg<S>>,
        // a incomplete_block is a block with a None prevblock (ie, Estimate) AND is
        // not a genesis_block
        incomplete_block: Block<S>,
    ) -> Self {
        let prevblock = prevblock_msg.map(|m| Block::from(&m));
        let block = Block::from(ProtoBlock {
            prevblock,
            ..((**incomplete_block.arc()).clone())
        });
        block
    }

    /// Math definition of blockchain membership
    pub fn is_member(&self, rhs: &Self) -> bool {
        self == rhs
            || rhs
                .prevblock()
                .as_ref()
                .map(|prevblock| self.is_member(prevblock))
                .unwrap_or(false)
    }

    pub fn safety_oracles(
        block: Block<S>,
        latest_msgs_honest: &LatestMsgsHonest<BlockMsg<S>>,
        equivocators: &HashSet<<BlockMsg<S> as CasperMsg>::Sender>,
        safety_oracle_threshold: WeightUnit,
        weights: &SendersWeight<S>,
    ) -> HashSet<BTreeSet<<BlockMsg<S> as CasperMsg>::Sender>> {
        fn latest_in_justification<S: Sender>(
            j: &Justification<BlockMsg<S>>,
            equivocators: &HashSet<<BlockMsg<S> as CasperMsg>::Sender>,
        ) -> HashMap<<BlockMsg<S> as CasperMsg>::Sender, BlockMsg<S>> {
            LatestMsgsHonest::from_latest_msgs(&LatestMsgs::from(j), equivocators)
                .iter()
                .map(|m| (m.sender().clone(), m.clone()))
                .collect()
        }

        let latest_containing_block: HashSet<&BlockMsg<S>> = latest_msgs_honest
            .iter()
            .filter(|&msg| block.is_member(&Block::from(msg)))
            .collect();

        let latest_agreeing_in_sender_view: HashMap<S, HashMap<S, BlockMsg<S>>> =
            latest_containing_block
                .iter()
                .map(|m| {
                    (
                        m.sender().clone(),
                        latest_in_justification(m.justification(), equivocators)
                            .into_iter()
                            .filter(|(_sender, msg)| block.is_member(&Block::from(msg)))
                            .collect(),
                    )
                })
                .collect();

        let neighbours: HashMap<&S, HashSet<&S>> = latest_agreeing_in_sender_view
            .iter()
            .map(|(sender, seen_agreeing)| {
                (
                    sender,
                    seen_agreeing
                        .keys()
                        .filter(|senderb| {
                            // println!("Some {:?}", senderb);
                            if latest_agreeing_in_sender_view.contains_key(senderb) {
                                latest_agreeing_in_sender_view[senderb]
                                    .contains_key(&sender.clone())
                            } else {
                                false
                            }
                        })
                        .collect(),
                )
            })
            .collect();
        // println!("neighbours: {:?}", neighbours);
        fn bron_kerbosch<S: Sender>(
            r: HashSet<&S>,
            p: HashSet<&S>,
            x: HashSet<&S>,
            mx_clqs: &mut HashSet<BTreeSet<S>>,
            neighbours: HashMap<&S, HashSet<&S>>,
        ) {
            // println!("recursed");
            if p.is_empty() && x.is_empty() {
                let rnew: BTreeSet<S> = r.into_iter().map(|x| x.clone()).collect();
                mx_clqs.insert(rnew);
            } else {
                let piter = p.clone();
                let mut p = p;
                let mut x = x;
                piter.into_iter().for_each(|i| {
                    p.remove(i);
                    let mut rnew = r.clone();
                    rnew.insert(i);
                    let pnew: HashSet<&S> = p.intersection(&neighbours[i]).cloned().collect();
                    let xnew: HashSet<&S> = x.intersection(&neighbours[i]).cloned().collect();
                    x.insert(i);
                    bron_kerbosch(rnew, pnew, xnew, mx_clqs, neighbours.clone())
                })
            }
        }

        let p = neighbours.iter().fold(HashSet::new(), |acc, (_sender, x)| {
            acc.union(x).cloned().collect()
        });

        let mut mx_clqs = HashSet::new();

        bron_kerbosch(HashSet::new(), p, HashSet::new(), &mut mx_clqs, neighbours);

        mx_clqs
            .into_iter()
            .filter(|x| {
                x.iter().fold(WeightUnit::ZERO, |acc, sender| {
                    acc + weights.weight(sender).unwrap_or(::std::f64::NAN)
                }) > safety_oracle_threshold
            })
            .collect()
    }

    // pub fn set_as_final(&mut self) -> () {
    //     let mut proto_block = (**self.0).clone();
    //     proto_block.prevblock = None;
    //     *self.0 = Arc::new(proto_block);
    // }

    pub fn prevblock(&self) -> Option<Self> {
        self.arc().prevblock.as_ref().cloned()
    }

    /// parses blockchain using the latest honest messages
    /// the return value is a tuple containing a map and a set
    /// the hashmap maps blocks to their respective children
    /// the set contains all the blocks that have a None
    /// as their prevblock (aka genesis blocks or finalized blocks)
    pub fn parse_blockchains(
        latest_msgs: &LatestMsgsHonest<BlockMsg<S>>,
    ) -> (
        HashMap<Block<S>, HashSet<Block<S>>>,
        HashSet<Block<S>>,
        HashMap<Block<S>, S>,
    ) {
        let latest_blocks: HashMap<Block<S>, S> = latest_msgs
            .iter()
            .map(|msg| (Block::from(msg), msg.sender().clone()))
            .collect();
        // start at the tip of the blockchain
        let mut visited_parents: HashMap<Block<S>, HashSet<Block<S>>> = latest_msgs
            .iter()
            .map(|msg| {
                let parent = Block::from(msg);
                let children = HashSet::new();
                (parent, children)
            })
            .collect();

        let mut queue: VecDeque<Block<S>> = visited_parents.keys().cloned().collect();
        let mut genesis: HashSet<Block<S>> = HashSet::new();
        let mut was_empty = false;
        // while there are still unvisited blocks
        while let Some(child) = queue.pop_front() {
            match (child.prevblock(), was_empty && genesis.is_empty()) {
                // if the prevblock is set, update the visited_parents map
                (Some(parent), false) => {
                    if queue.is_empty() {
                        was_empty = true
                    }
                    if visited_parents.contains_key(&parent) {
                        // visited parent before, fork found, add new child and don't add parent to queue (since it is already in the queue)
                        visited_parents.get_mut(&parent).map(|parents_children| {
                            parents_children.insert(child);
                        });
                    } else {
                        // didn't visit parent before, add it with known child, and push to queue
                        let mut parents_children = HashSet::new();
                        parents_children.insert(child);
                        visited_parents.insert(parent.clone(), parents_children);
                        queue.push_back(parent);
                    }
                }
                // if not, update the genesis set, as a None prevblock indicates the genesis
                _ => {
                    genesis.insert(child);
                }
            };
        }
        (visited_parents, genesis, latest_blocks)
    }
    /// used to collect the validators that produced blocks for each side of a fork
    fn collect_validators(
        block: &Block<S>,
        visited: &HashMap<Block<S>, HashSet<Block<S>>>,
        // mut acc: HashSet<S>,
        latest_blocks: &HashMap<Block<S>, S>,
        b_in_lms_senders: Rc<RwLock<HashMap<Block<S>, HashSet<S>>>>,
    ) -> HashSet<S> {
        let mut senders = HashSet::new();
        // collect this sender if this block is his proposed one from his latest
        // message
        latest_blocks
            .get(block)
            .map(|sender| senders.insert(sender.clone()));
        let res = visited
            .get(block)
            .map(|children| {
                children.iter().fold(senders.clone(), |acc, child| {
                    let res = Self::collect_validators(
                        child,
                        visited,
                        latest_blocks,
                        b_in_lms_senders.clone(),
                    );
                    res.union(&acc).cloned().collect()
                })
            })
            .unwrap_or_else(|| senders);
        b_in_lms_senders
            .write()
            .ok()
            .map(|mut lms| lms.insert(block.clone(), res.clone()));
        res
    }

    /// find heaviest block
    fn pick_heaviest(
        blocks: &HashSet<Block<S>>,
        visited: &HashMap<Block<S>, HashSet<Block<S>>>,
        weights: &SendersWeight<S>,
        latest_blocks: &HashMap<Block<S>, S>,
        b_in_lms_senders: Rc<RwLock<HashMap<Block<S>, HashSet<S>>>>,
    ) -> Option<(Option<Self>, WeightUnit, HashSet<Self>)> {
        let init = Some((None, WeightUnit::ZERO, HashSet::new()));
        let heaviest_child = match blocks.len() {
            // only one choice, no need to compute anything
            l if l == 1 => blocks.iter().next().cloned().and_then(|block| {
                visited
                    .get(&block)
                    .map(|children| (Some(block), WeightUnit::ZERO, children.clone()))
            }),
            // fork, need to find best block
            l if l > 1 => blocks.iter().fold(init, |best, block| {
                let best_children =
                    best.and_then(|best| visited.get(&block).map(|children| (best, children)));
                best_children.and_then(|((b_block, b_weight, b_children), children)| {
                    let referred_senders = match b_in_lms_senders
                        .read()
                        .ok()
                        .and_then(|lms| lms.get(block).cloned())
                    {
                        Some(rs) => rs,
                        None => Self::collect_validators(
                            block,
                            visited,
                            latest_blocks,
                            b_in_lms_senders.clone(),
                        ),
                    };
                    let weight = weights.sum_weight_senders(&referred_senders);
                    let res = Some((Some(block.clone()), weight, children.clone()));
                    let b_res = Some((b_block.clone(), b_weight, b_children));
                    if weight > b_weight {
                        res
                    } else if weight < b_weight {
                        b_res
                    } else {
                        // break ties with blockhash
                        let ord = b_block.as_ref().map(|b| b.id().cmp(block.id()));
                        match ord {
                            Some(std::cmp::Ordering::Greater) => res,
                            Some(std::cmp::Ordering::Less) => b_res,
                            Some(std::cmp::Ordering::Equal) => b_res,
                            None => None,
                        }
                    }
                })
            }),
            _ => None,
        };
        heaviest_child.and_then(|(b_block, b_weight, b_children)| {
            if b_children.is_empty() {
                // base case
                Some((b_block, b_weight, b_children))
            } else {
                // recurse
                Self::pick_heaviest(
                    &b_children,
                    visited,
                    &weights,
                    latest_blocks,
                    b_in_lms_senders.clone(),
                )
            }
        })
    }

    pub fn ghost(
        latest_msgs: &LatestMsgsHonest<BlockMsg<S>>,
        senders_weights: &SendersWeight<<BlockMsg<S> as CasperMsg>::Sender>,
    ) -> Result<Self, &'static str> {
        let (visited, genesis, latest_blocks) = Self::parse_blockchains(latest_msgs);
        let b_in_lms_senders = Rc::new(RwLock::new(HashMap::<Block<S>, HashSet<S>>::new()));
        Block::pick_heaviest(
            &genesis,
            &visited,
            senders_weights,
            &latest_blocks,
            b_in_lms_senders,
        )
        .and_then(|(opt_block, ..)| opt_block)
        .ok_or_else(|| "Failed to get prevblock using ghost.")
    }
}

impl<S: Sender> Estimate for Block<S> {
    type M = BlockMsg<S>;

    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        senders_weights: &SendersWeight<<<Self as Estimate>::M as CasperMsg>::Sender>,
        _data: Option<<Self as Data>::Data>,
    ) -> Result<Self, &'static str> {
        let prevblock = Block::ghost(latest_msgs, senders_weights)?;
        Ok(Block::from(ProtoBlock::new(Some(prevblock))))
    }
}

#[cfg(test)]
mod tests {
    use std::iter;
    use std::iter::FromIterator;

    use super::*;
    use justification::{Justification, LatestMsgs, SenderState};

    #[test]
    fn example_usage() {
        let (sender0, sender1, sender2, sender3, sender4) = (0, 1, 2, 3, 4); // miner identities
        let (weight0, weight1, weight2, weight3, weight4) = (1.0, 1.0, 2.0, 1.0, 1.1); // and their corresponding sender_state
        let senders_weights = SendersWeight::new(
            [
                (sender0, weight0),
                (sender1, weight1),
                (sender2, weight2),
                (sender3, weight3),
                (sender4, weight4),
            ]
            .iter()
            .cloned()
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

        // let txs = BTreeSet::new();

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
        let genesis_block = Block::from(ProtoBlock::new(None));
        let latest_msgs = Justification::new();
        let genesis_block_msg = BlockMsg::new(sender0, latest_msgs, genesis_block.clone(), None);
        assert_eq!(
            &Block::from(&genesis_block_msg),
            &genesis_block,
            "genesis block with None as prevblock"
        );

        let proto_b1 = Block::new(None);
        let (m1, _) = BlockMsg::from_msgs(
            sender1,
            vec![&genesis_block_msg],
            &sender_state,
            Some(proto_b1), // data
        )
        .unwrap();

        let proto_b2 = Block::new(None);
        let (m2, _) = BlockMsg::from_msgs(
            sender2,
            vec![&genesis_block_msg],
            &sender_state,
            Some(proto_b2),
        )
        .unwrap();

        let proto_b3 = Block::new(None);
        let (m3, _) =
            BlockMsg::from_msgs(sender3, vec![&m1, &m2], &sender_state, Some(proto_b3)).unwrap();

        assert_eq!(
            m3.estimate(),
            &Block::new(Some(Block::from(&m2))),
            "should build on top of m2 as sender2 has more weight"
        );

        let proto_b4 = Block::new(None);
        let (m4, _) =
            BlockMsg::from_msgs(sender4, vec![&m1], &sender_state, Some(proto_b4)).unwrap();

        assert_eq!(
            m4.estimate(),
            &Block::new(Some(Block::from(&m1))),
            "should build on top of m1 as as thats the only msg it saw"
        );

        let proto_b5 = Block::new(None);
        // println!("\n3 {:?}", m3);
        // println!("\n4 {:?}", m4);
        let (m5, _) =
            BlockMsg::from_msgs(sender0, vec![&m3, &m2], &sender_state, Some(proto_b5)).unwrap();
        // println!("\nm5 {:?}", m5);
        // println!("\nm5_estimate {:?}", Block::from(&m5));

        // println!();
        assert_eq!(
            m5.estimate(),
            &Block::new(Some(Block::from(&m3))),
            "should build on top of "
        );

        let block = Block::from(&m3);
        assert_eq!(block, Block::new(Some(Block::from(&m2))),);
        // assert_eq!(block.prevblock(), Some(genesis_block),);
    }

    #[test]
    fn test2() {
        let (senderg, sender0, sender1, sender2, sender3, sender4, sender5) = (0, 1, 2, 3, 4, 5, 6); // miner identities
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
            ]
            .iter()
            .cloned()
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

        // let txs = BTreeSet::new();

        // block dag
        let genesis_block = Block::from(ProtoBlock::new(None));
        let latest_msgs = Justification::new();
        let genesis_block_msg = BlockMsg::new(senderg, latest_msgs, genesis_block.clone(), None);
        // assert_eq!(
        //     &Block::from(&genesis_block_msg),
        //     &genesis_block,
        //     "genesis block with None as prevblock"
        // );
        let proto_b0 = Block::new(None);
        let (m0, sender_state) = BlockMsg::from_msgs(
            sender0,
            vec![&genesis_block_msg],
            &sender_state,
            Some(proto_b0), // data
        )
        .unwrap();

        let proto_b1 = Block::new(None);
        let (m1, sender_state) =
            BlockMsg::from_msgs(sender1, vec![&m0], &sender_state, Some(proto_b1)).unwrap();

        let proto_b2 = Block::new(None);
        let (m2, sender_state) = BlockMsg::from_msgs(
            sender2,
            vec![&genesis_block_msg],
            &sender_state,
            Some(proto_b2),
        )
        .unwrap();

        // assert_eq!(
        //     m2.estimate(),
        //     &Block::new(Some(Block::from(&m1)), sender2),
        //     "should build on top of m1 as sender1 has more weight"
        // );

        let proto_b3 = Block::new(None);
        let (m3, sender_state) =
            BlockMsg::from_msgs(sender3, vec![&m2], &sender_state, Some(proto_b3)).unwrap();

        // assert_eq!(
        //     m3.estimate(),
        //     &Block::new(Some(Block::from(&m0)), sender3),
        //     "should build on top of m0 as as thats the only msg it saw"
        // );

        let proto_b4 = Block::new(None);
        // println!("\n3 {:?}", m2);
        // println!("\n4 {:?}", m3);
        let (m4, sender_state) =
            BlockMsg::from_msgs(sender4, vec![&m2], &sender_state, Some(proto_b4)).unwrap();
        // assert_eq!(
        //     m4.estimate(),
        //     &Block::new(Some(Block::from(&m2)), sender4),
        //     "should build on top of "
        // );

        let proto_b5 = Block::new(None);

        let (m5, _) = BlockMsg::from_msgs(
            sender5,
            vec![&m0, &m1, &m2, &m3, &m4],
            &sender_state,
            Some(proto_b5),
        )
        .unwrap();

        assert_eq!(
            m5.estimate(),
            &Block::new(Some(Block::from(&m4))),
            "should build on top of b4"
        );
    }

    #[test]
    fn safety_oracles() {
        let nodes = 3;
        let senders: Vec<u32> = (0..nodes).collect();
        let weights: Vec<f64> = iter::repeat(1.0).take(nodes as usize).collect();

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

        // let txs = BTreeSet::new();

        // block dag
        let proto_b0 = Block::from(ProtoBlock::new(None));
        let latest_msgs = Justification::new();
        let m0 = BlockMsg::new(senders[0], latest_msgs, proto_b0.clone(), None);

        let proto_b1 = Block::new(Some(proto_b0.clone()));
        let (m1, sender_state) =
            BlockMsg::from_msgs(senders[1], vec![&m0], &sender_state, Some(proto_b1.clone()))
                .unwrap();

        let proto_b2 = Block::new(Some(proto_b1.clone()));
        let (m2, sender_state) =
            BlockMsg::from_msgs(senders[0], vec![&m1], &sender_state, Some(proto_b2.clone()))
                .unwrap();

        // no clique yet, since senders[1] has not seen senders[0] seeing senders[1] having proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.latests_msgs(),
                    sender_state.equivocators()
                ),
                sender_state.equivocators(),
                2.0,
                &senders_weights
            ),
            HashSet::new()
        );

        let proto_b3 = Block::new(Some(proto_b2.clone()));
        let (m3, sender_state) =
            BlockMsg::from_msgs(senders[1], vec![&m2], &sender_state, Some(proto_b3.clone()))
                .unwrap();

        // clique, since both senders have seen each other having proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.latests_msgs(),
                    sender_state.equivocators()
                ),
                sender_state.equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![senders[0], senders[1]])])
        );

        let proto_b4 = Block::new(Some(proto_b3.clone()));
        let (m4, sender_state) =
            BlockMsg::from_msgs(senders[2], vec![&m3], &sender_state, Some(proto_b4.clone()))
                .unwrap();

        let proto_b5 = Block::new(Some(proto_b4.clone()));
        let (m5, sender_state) =
            BlockMsg::from_msgs(senders[1], vec![&m4], &sender_state, Some(proto_b5.clone()))
                .unwrap();

        // no second clique yet, since senders[2] has not seen senders[1] seeing senders[2] having proto_b0.clone() in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.latests_msgs(),
                    sender_state.equivocators()
                ),
                sender_state.equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![senders[0], senders[1]])])
        );

        let proto_b6 = Block::new(Some(proto_b5.clone()));
        let (m6, sender_state) =
            BlockMsg::from_msgs(senders[2], vec![&m5], &sender_state, Some(proto_b5.clone()))
                .unwrap();

        // have two cliques on proto_b0 now
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.latests_msgs(),
                    sender_state.equivocators()
                ),
                sender_state.equivocators(),
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
                    sender_state.latests_msgs(),
                    sender_state.equivocators()
                ),
                sender_state.equivocators(),
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
                    sender_state.latests_msgs(),
                    sender_state.equivocators()
                ),
                sender_state.equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![senders[1], senders[2]])])
        );

        let proto_b7 = Block::new(Some(proto_b6.clone()));
        let (m7, sender_state) =
            BlockMsg::from_msgs(senders[0], vec![&m6], &sender_state, Some(proto_b6.clone()))
                .unwrap();

        let proto_b8 = Block::new(Some(proto_b7.clone()));
        let (m8, sender_state) =
            BlockMsg::from_msgs(senders[2], vec![&m7], &sender_state, Some(proto_b7.clone()))
                .unwrap();

        let (_, sender_state) =
            BlockMsg::from_msgs(senders[0], vec![&m8], &sender_state, Some(proto_b8.clone()))
                .unwrap();

        // now entire network is clique
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.latests_msgs(),
                    sender_state.equivocators()
                ),
                sender_state.equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                senders[0], senders[1], senders[2],
            ])])
        );
        assert_eq!(
            Block::safety_oracles(
                proto_b2.clone(),
                &LatestMsgsHonest::from_latest_msgs(
                    sender_state.latests_msgs(),
                    sender_state.equivocators()
                ),
                sender_state.equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                senders[0], senders[1], senders[2],
            ])])
        );
    }
}
