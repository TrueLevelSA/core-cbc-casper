// Core CBC Rust Library
// Copyright (C) 2018  Coordination Technology Ltd.
// Authors: pZ4 <pz4@protonmail.ch>,
//          Lederstrumpf,
//          h4sh3d <h4sh3d@truelevel.io>
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::convert::From;
use std::iter::Iterator;
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::{Arc, RwLock};

use serde_derive::Serialize;

use crate::estimator::Estimate;
use crate::justification::{Justification, LatestMsgs, LatestMsgsHonest};
use crate::message::{self, Trait as MTrait};
use crate::sender;
use crate::util::hash::Hash;
use crate::util::id::Id;
use crate::util::weight::{WeightUnit, Zero};

/// Casper message (`message::Message`) for a `Block` send by a validator `S: sender::Trait`
pub type Message<S> = message::Message<Block<S> /*Estimate*/, S /*Sender*/>;

#[derive(Clone, Eq, PartialEq, Debug, Hash, Serialize)]
struct ProtoBlock<S: sender::Trait> {
    prevblock: Option<Block<S>>,
    sender_type: PhantomData<S>,
}

impl<S: sender::Trait> ProtoBlock<S> {
    pub fn new(prevblock: Option<Block<S>>) -> ProtoBlock<S> {
        ProtoBlock {
            prevblock,
            sender_type: PhantomData,
        }
    }
}

/// Simplest structure of a block with a `prevblock` pointer for runing Casper on a blockchain.
#[derive(Clone, Eq, Hash)]
pub struct Block<S: sender::Trait>(Arc<ProtoBlock<S>>);

#[cfg(feature = "integration_test")]
impl<S: sender::Trait + Into<S>> From<S> for Block<S> {
    fn from(_sender: S) -> Self {
        Block::from(ProtoBlock::new(None))
    }
}

impl<S: sender::Trait> std::fmt::Debug for Block<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{:?} -> {:?}",
            self.getid(),
            self.prevblock()
                .as_ref()
                .map(|p| p.getid())
                .unwrap_or(Hash::default())
        )
    }
}

impl<S: sender::Trait> serde::Serialize for Block<S> {
    fn serialize<T: serde::Serializer>(&self, rhs: T) -> Result<T::Ok, T::Error> {
        use serde::ser::SerializeStruct;
        let mut msg = rhs.serialize_struct("Block", 1)?;
        msg.serialize_field("prevblock", &self.prevblock())?;
        msg.end()
    }
}

impl<S: sender::Trait> Id for Block<S> {
    type ID = Hash;
}

impl<S: sender::Trait> PartialEq for Block<S> {
    fn eq(&self, rhs: &Self) -> bool {
        Arc::ptr_eq(self.arc(), rhs.arc()) || self.getid() == rhs.getid()
    }
}

impl<S: sender::Trait> From<ProtoBlock<S>> for Block<S> {
    fn from(protoblock: ProtoBlock<S>) -> Self {
        Block(Arc::new(protoblock))
    }
}

impl<'z, S: sender::Trait> From<&'z Message<S>> for Block<S> {
    fn from(msg: &Message<S>) -> Self {
        msg.estimate().clone()
    }
}

impl<S: sender::Trait> Estimate for Block<S> {
    type M = Message<S>;

    fn mk_estimate<U: WeightUnit>(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        senders_weights: &sender::Weights<<<Self as Estimate>::M as message::Trait>::Sender, U>,
    ) -> Result<Self, &'static str> {
        let prevblock = Block::ghost(latest_msgs, senders_weights)?;
        Ok(Block::from(ProtoBlock::new(Some(prevblock))))
    }
}

impl<S: sender::Trait> Block<S> {
    pub fn new(prevblock: Option<Block<S>>) -> Self {
        Block::from(ProtoBlock::new(prevblock))
    }

    fn arc(&self) -> &Arc<ProtoBlock<S>> {
        &self.0
    }

    /// Create a new block from a prevblock message and an incomplete block.
    pub fn from_prevblock_msg(
        prevblock_msg: Option<Message<S>>,
        // a incomplete_block is a block with a None prevblock (ie, Estimate) AND is not a
        // genesis_block
        incomplete_block: Block<S>,
    ) -> Self {
        let prevblock = prevblock_msg.map(|m| Block::from(&m));
        let block = Block::from(ProtoBlock {
            prevblock,
            ..((**incomplete_block.arc()).clone())
        });
        block
    }

    /// Mathematical definition of blockchain membership.
    pub fn is_member(&self, rhs: &Self) -> bool {
        self == rhs
            || rhs
                .prevblock()
                .as_ref()
                .map(|prevblock| self.is_member(prevblock))
                .unwrap_or(false)
    }

    pub fn safety_oracles<U: WeightUnit>(
        block: Block<S>,
        latest_msgs_honest: &LatestMsgsHonest<Message<S>>,
        equivocators: &HashSet<<Message<S> as message::Trait>::Sender>,
        safety_oracle_threshold: U,
        weights: &sender::Weights<S, U>,
    ) -> HashSet<BTreeSet<<Message<S> as message::Trait>::Sender>> {
        fn latest_in_justification<S: sender::Trait>(
            j: &Justification<Message<S>>,
            equivocators: &HashSet<<Message<S> as message::Trait>::Sender>,
        ) -> HashMap<<Message<S> as message::Trait>::Sender, Message<S>> {
            LatestMsgsHonest::from_latest_msgs(&LatestMsgs::from(j), equivocators)
                .iter()
                .map(|m| (m.sender().clone(), m.clone()))
                .collect()
        }

        let latest_containing_block: HashSet<&Message<S>> = latest_msgs_honest
            .iter()
            .filter(|&msg| block.is_member(&Block::from(msg)))
            .collect();

        let latest_agreeing_in_sender_view: HashMap<S, HashMap<S, Message<S>>> =
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

        fn bron_kerbosch<S: sender::Trait>(
            r: HashSet<&S>,
            p: HashSet<&S>,
            x: HashSet<&S>,
            mx_clqs: &mut HashSet<BTreeSet<S>>,
            neighbours: HashMap<&S, HashSet<&S>>,
        ) {
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
                x.iter().fold(<U as Zero<U>>::ZERO, |acc, sender| {
                    // FIXME: U::default() or <U ...>::Zero? or U::NAN
                    acc + weights.weight(sender).unwrap_or(U::NAN)
                }) > safety_oracle_threshold
            })
            .collect()
    }

    pub fn prevblock(&self) -> Option<Self> {
        self.arc().prevblock.as_ref().cloned()
    }

    /// Parses blockchain using the latest honest messages the return value is a tuple containing a
    /// map and a set. The hashmap maps blocks to their respective children. The set contains all
    /// the blocks that have a None as their prevblock (aka genesis blocks or finalized blocks).
    pub fn parse_blockchains(
        latest_msgs: &LatestMsgsHonest<Message<S>>,
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
                        // visited parent before, fork found, add new child and don't add parent to
                        // queue (since it is already in the queue)
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

    /// Collects the validators that produced blocks for each side of a fork.
    fn collect_validators(
        block: &Block<S>,
        visited: &HashMap<Block<S>, HashSet<Block<S>>>,
        latest_blocks: &HashMap<Block<S>, S>,
        b_in_lms_senders: Rc<RwLock<HashMap<Block<S>, HashSet<S>>>>,
    ) -> HashSet<S> {
        let mut senders = HashSet::new();
        // collect this sender if this block is his proposed one from his latest message
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

    /// Find heaviest block.
    fn pick_heaviest<U: WeightUnit>(
        blocks: &HashSet<Block<S>>,
        visited: &HashMap<Block<S>, HashSet<Block<S>>>,
        weights: &sender::Weights<S, U>,
        latest_blocks: &HashMap<Block<S>, S>,
        b_in_lms_senders: Rc<RwLock<HashMap<Block<S>, HashSet<S>>>>,
    ) -> Option<(Option<Self>, U, HashSet<Self>)> {
        let init = Some((None, <U as Zero<U>>::ZERO, HashSet::new()));
        let heaviest_child = match blocks.len() {
            // only one choice, no need to compute anything
            l if l == 1 => blocks.iter().next().cloned().and_then(|block| {
                visited
                    .get(&block)
                    .map(|children| (Some(block), <U as Zero<U>>::ZERO, children.clone()))
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
                        let ord = b_block.as_ref().map(|b| b.getid().cmp(&block.getid()));
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

    pub fn ghost<U: WeightUnit>(
        latest_msgs: &LatestMsgsHonest<Message<S>>,
        senders_weights: &sender::Weights<<Message<S> as message::Trait>::Sender, U>,
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

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashSet};
    use std::iter;
    use std::iter::FromIterator;

    use crate::blockchain::{Block, Message, ProtoBlock};
    use crate::justification::{Justification, LatestMsgs, LatestMsgsHonest};
    use crate::message::Trait;
    use crate::sender;

    #[test]
    fn partial_view() {
        // Test cases where not all validators see all messages.
        let (sender0, sender1, sender2, sender3, sender4) = (0, 1, 2, 3, 4);
        let (weight0, weight1, weight2, weight3, weight4) = (1.0, 1.0, 2.0, 1.0, 1.1);
        let senders_weights = sender::Weights::new(
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
        let state = sender::State::new(
            senders_weights.clone(),
            0.0,  // state fault weight
            None, // latest messages
            LatestMsgs::empty(),
            1.0,            // subjective fault weight threshold
            HashSet::new(), // equivocators
        );

        let genesis_block = Block::from(ProtoBlock::new(None));
        let latest_msgs = Justification::empty();
        let genesis_block_msg = Message::new(sender0, latest_msgs, genesis_block.clone());
        // (s0, w=1.0)   gen
        // (s1, w=1.0)
        // (s2, w=2.0)
        // (s3, w=1.0)
        // (s4, w=1.1)

        assert_eq!(
            &Block::from(&genesis_block_msg),
            &genesis_block,
            "genesis block with None as prevblock"
        );

        let (m1, _) = Message::from_msgs(sender1, vec![&genesis_block_msg], &state).unwrap();
        // (s0, w=1.0)   gen
        // (s1, w=1.0)     \--m1
        // (s2, w=2.0)
        // (s3, w=1.0)
        // (s4, w=1.1)

        let (m2, _) = Message::from_msgs(sender2, vec![&genesis_block_msg], &state).unwrap();
        // (s0, w=1.0)   gen
        // (s1, w=1.0)    |\--m1
        // (s2, w=2.0)    \---m2
        // (s3, w=1.0)
        // (s4, w=1.1)

        let (m3, _) = Message::from_msgs(sender3, vec![&m1, &m2], &state).unwrap();
        // (s0, w=1.0)   gen
        // (s1, w=1.0)    |\--m1
        // (s2, w=2.0)    \---m2
        // (s3, w=1.0)         \---m3
        // (s4, w=1.1)

        assert_eq!(
            m3.estimate(),
            &Block::new(Some(Block::from(&m2))),
            "should build on top of m2 as sender2 has more weight"
        );

        let (m4, _) = Message::from_msgs(sender4, vec![&m1], &state).unwrap();
        // (s0, w=1.0)   gen
        // (s1, w=1.0)    |\--m1-------\
        // (s2, w=2.0)    \---m2       |
        // (s3, w=1.0)         \---m3  |
        // (s4, w=1.1)                 m4

        assert_eq!(
            m4.estimate(),
            &Block::new(Some(Block::from(&m1))),
            "should build on top of m1 as thats the only msg it saw"
        );

        let (m5, _) = Message::from_msgs(sender0, vec![&m3, &m2], &state).unwrap();
        // (s0, w=1.0)   gen               m5
        // (s1, w=1.0)    |\--m1-------\   |
        // (s2, w=2.0)    \---m2       |   |
        // (s3, w=1.0)         \---m3--|---/
        // (s4, w=1.1)                 m4

        assert_eq!(
            m5.estimate(),
            &Block::new(Some(Block::from(&m3))),
            "should build on top of m3"
        );

        let block = Block::from(&m3);
        assert_eq!(block, Block::new(Some(Block::from(&m2))));
    }

    #[test]
    fn full_view() {
        // Test a case where the last validator see all messages and build on top of the heaviest
        // one.
        let (senderg, sender0, sender1, sender2, sender3, sender4, sender5) = (0, 1, 2, 3, 4, 5, 6);
        let (weightg, weight0, weight1, weight2, weight3, weight4, weight5) =
            (1.0, 1.0, 1.0, 1.0, 1.0, 1.1, 1.0);

        let senders_weights = sender::Weights::new(
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

        let state = sender::State::new(
            senders_weights.clone(),
            0.0,  // state fault weight
            None, // latest messages
            LatestMsgs::empty(),
            1.0,            // subjective fault weight threshold
            HashSet::new(), // equivocators
        );

        let genesis_block = Block::from(ProtoBlock::new(None));
        let latest_msgs = Justification::empty();
        let genesis_block_msg = Message::new(senderg, latest_msgs, genesis_block.clone());
        // (sg, w=1.0)   gen
        // (s0, w=1.0)
        // (s1, w=1.0)
        // (s2, w=1.0)
        // (s3, w=1.0)
        // (s4, w=1.1)
        // (s5, w=1.0)

        let (m0, _) = Message::from_msgs(sender0, vec![&genesis_block_msg], &state).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)     \--m0
        // (s1, w=1.0)
        // (s2, w=1.0)
        // (s3, w=1.0)
        // (s4, w=1.1)
        // (s5, w=1.0)

        let (m1, _) = Message::from_msgs(sender1, vec![&m0], &state).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)     \--m0
        // (s1, w=1.0)         \--m1
        // (s2, w=1.0)
        // (s3, w=1.0)
        // (s4, w=1.1)
        // (s5, w=1.0)

        let (m2, _) = Message::from_msgs(sender2, vec![&genesis_block_msg], &state).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)    |\--m0
        // (s1, w=1.0)    |    \--m1
        // (s2, w=1.0)    \-----------m2
        // (s3, w=1.0)
        // (s4, w=1.1)
        // (s5, w=1.0)

        let (m3, _) = Message::from_msgs(sender3, vec![&m2], &state).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)    |\--m0
        // (s1, w=1.0)    |    \--m1
        // (s2, w=1.0)    \-----------m2
        // (s3, w=1.0)                 \--m3
        // (s4, w=1.1)
        // (s5, w=1.0)

        let (m4, _) = Message::from_msgs(sender4, vec![&m2], &state).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)    |\--m0
        // (s1, w=1.0)    |    \--m1
        // (s2, w=1.0)    \-----------m2
        // (s3, w=1.0)                |\--m3
        // (s4, w=1.1)                \-------m4
        // (s5, w=1.0)

        let (m5, _) = Message::from_msgs(sender5, vec![&m0, &m1, &m2, &m3, &m4], &state).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)    |\--m0
        // (s1, w=1.0)    |    \--m1
        // (s2, w=1.0)    \-----------m2
        // (s3, w=1.0)                |\--m3
        // (s4, w=1.1)                \-------m4
        // (s5, w=1.0)                         \--m5

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

        let senders_weights = sender::Weights::new(
            senders
                .iter()
                .cloned()
                .zip(weights.iter().cloned())
                .collect(),
        );

        let state = sender::State::new(
            senders_weights.clone(),
            0.0,  // state fault weight
            None, // latest messages
            LatestMsgs::empty(),
            1.0,            // subjective fault weight threshold
            HashSet::new(), // equivocators
        );

        // block dag
        let proto_b0 = Block::from(ProtoBlock::new(None));
        let latest_msgs = Justification::empty();
        let m0 = Message::new(senders[0], latest_msgs, proto_b0.clone());

        let proto_b1 = Block::new(Some(proto_b0.clone()));
        let (m1, state) = Message::from_msgs(senders[1], vec![&m0], &state).unwrap();

        let proto_b2 = Block::new(Some(proto_b1.clone()));
        let (m2, state) = Message::from_msgs(senders[0], vec![&m1], &state).unwrap();

        // no clique yet, since senders[1] has not seen senders[0] seeing senders[1] having
        // proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                2.0,
                &senders_weights
            ),
            HashSet::new()
        );

        let (m3, state) = Message::from_msgs(senders[1], vec![&m2], &state).unwrap();

        // clique, since both senders have seen each other having proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![senders[0], senders[1]])])
        );

        let (m4, state) = Message::from_msgs(senders[2], vec![&m3], &state).unwrap();

        let (m5, state) = Message::from_msgs(senders[1], vec![&m4], &state).unwrap();

        // no second clique yet, since senders[2] has not seen senders[1] seeing senders[2] having
        // proto_b0.clone() in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![senders[0], senders[1]])])
        );

        let (m6, state) = Message::from_msgs(senders[2], vec![&m5], &state).unwrap();

        // have two cliques on proto_b0 now
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
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
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
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
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![senders[1], senders[2]])])
        );

        let (m7, state) = Message::from_msgs(senders[0], vec![&m6], &state).unwrap();

        let (m8, state) = Message::from_msgs(senders[2], vec![&m7], &state).unwrap();

        let (_, state) = Message::from_msgs(senders[0], vec![&m8], &state).unwrap();

        // now entire network is clique
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
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
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &senders_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                senders[0], senders[1], senders[2],
            ])])
        );
    }
}
