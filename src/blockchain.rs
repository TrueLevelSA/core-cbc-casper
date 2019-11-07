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
use std::sync::Arc;

use serde_derive::Serialize;

use crate::estimator::Estimator;
use crate::justification::{Justification, LatestMsgs, LatestMsgsHonest};
use crate::message;
use crate::util::hash::Hash;
use crate::util::id::Id;
use crate::util::weight::{WeightUnit, Zero};
use crate::validator;

/// Casper message (`message::Message`) for a `Block` send by a validator `V:
/// validator::ValidatorName`
pub type Message<V> = message::Message<Block<V>>;

#[derive(Clone, Eq, PartialEq, Debug, Hash, Serialize)]
struct ProtoBlock<V: validator::ValidatorName> {
    prevblock: Option<Block<V>>,
    validator_type: PhantomData<V>,
}

impl<V: validator::ValidatorName> ProtoBlock<V> {
    pub fn new(prevblock: Option<Block<V>>) -> ProtoBlock<V> {
        ProtoBlock {
            prevblock,
            validator_type: PhantomData,
        }
    }
}

/// Simplest structure of a block with a `prevblock` pointer for runing Casper on a blockchain.
#[derive(Clone, Eq)]
pub struct Block<V: validator::ValidatorName>(Arc<ProtoBlock<V>>);

#[cfg(feature = "integration_test")]
impl<V: validator::ValidatorName + Into<V>> From<V> for Block<V> {
    fn from(_validator: V) -> Self {
        Block::from(ProtoBlock::new(None))
    }
}

impl<V: validator::ValidatorName> std::fmt::Debug for Block<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{:?} -> {:?}",
            self.getid(),
            self.prevblock()
                .as_ref()
                .map(|p| p.getid())
                .unwrap_or_default()
        )
    }
}

impl<V: validator::ValidatorName> serde::Serialize for Block<V> {
    fn serialize<T: serde::Serializer>(&self, rhs: T) -> Result<T::Ok, T::Error> {
        use serde::ser::SerializeStruct;
        let mut msg = rhs.serialize_struct("Block", 1)?;
        msg.serialize_field("prevblock", &self.prevblock())?;
        msg.end()
    }
}

impl<V: validator::ValidatorName> Id for Block<V> {
    type ID = Hash;
}

impl<V: validator::ValidatorName> std::hash::Hash for Block<V> {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        self.0.hash(hasher);
    }
}

impl<V: validator::ValidatorName> PartialEq for Block<V> {
    fn eq(&self, rhs: &Self) -> bool {
        Arc::ptr_eq(self.arc(), rhs.arc()) || self.getid() == rhs.getid()
    }
}

impl<V: validator::ValidatorName> From<ProtoBlock<V>> for Block<V> {
    fn from(protoblock: ProtoBlock<V>) -> Self {
        Block(Arc::new(protoblock))
    }
}

impl<'z, V: validator::ValidatorName> From<&'z Message<V>> for Block<V> {
    fn from(msg: &Message<V>) -> Self {
        msg.estimate().clone()
    }
}

#[derive(Debug)]
pub struct Error;

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "Failed to get prevblock using ghost")
    }
}

impl std::error::Error for Error {}

impl<V: validator::ValidatorName> Estimator for Block<V> {
    type Error = Error;
    type ValidatorName = V;

    fn estimate<U: WeightUnit>(
        latest_msgs: &LatestMsgsHonest<Self>,
        validators_weights: &validator::Weights<V, U>,
    ) -> Result<Self, Self::Error> {
        let prevblock = Block::ghost(latest_msgs, validators_weights)?;
        Ok(Block::from(ProtoBlock::new(Some(prevblock))))
    }
}

type BlocksChildrenMap<V> = HashMap<Block<V>, HashSet<Block<V>>>;
type GenesisBlocks<V> = HashSet<Block<V>>;
type BlocksValidatorsMap<V> = HashMap<Block<V>, V>;

impl<V: validator::ValidatorName> Block<V> {
    pub fn new(prevblock: Option<Block<V>>) -> Self {
        Block::from(ProtoBlock::new(prevblock))
    }

    fn arc(&self) -> &Arc<ProtoBlock<V>> {
        &self.0
    }

    /// Create a new block from a prevblock message and an incomplete block.
    pub fn from_prevblock_msg(
        prevblock_msg: Option<Message<V>>,
        // a incomplete_block is a block with a None prevblock (ie, Estimator) AND is not a
        // genesis_block
        incomplete_block: Block<V>,
    ) -> Self {
        let prevblock = prevblock_msg.map(|m| Block::from(&m));
        Block::from(ProtoBlock {
            prevblock,
            ..((**incomplete_block.arc()).clone())
        })
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
        block: Block<V>,
        latest_msgs_honest: &LatestMsgsHonest<Self>,
        equivocators: &HashSet<V>,
        safety_oracle_threshold: U,
        weights: &validator::Weights<V, U>,
    ) -> HashSet<BTreeSet<V>> {
        fn latest_in_justification<V: validator::ValidatorName>(
            j: &Justification<Block<V>>,
            equivocators: &HashSet<V>,
        ) -> HashMap<V, Message<V>> {
            LatestMsgsHonest::from_latest_msgs(&LatestMsgs::from(j), equivocators)
                .iter()
                .map(|m| (m.sender().clone(), m.clone()))
                .collect()
        }

        let latest_containing_block: HashSet<&Message<V>> = latest_msgs_honest
            .iter()
            .filter(|&msg| block.is_member(&Block::from(msg)))
            .collect();

        let latest_agreeing_in_validator_view: HashMap<V, HashMap<V, Message<V>>> =
            latest_containing_block
                .iter()
                .map(|m| {
                    (
                        m.sender().clone(),
                        latest_in_justification(m.justification(), equivocators)
                            .into_iter()
                            .filter(|(_validator, msg)| block.is_member(&Block::from(msg)))
                            .collect(),
                    )
                })
                .collect();

        let neighbours: HashMap<&V, HashSet<&V>> = latest_agreeing_in_validator_view
            .iter()
            .map(|(validator, seen_agreeing)| {
                (
                    validator,
                    seen_agreeing
                        .keys()
                        .filter(|validatorb| {
                            if latest_agreeing_in_validator_view.contains_key(validatorb) {
                                latest_agreeing_in_validator_view[validatorb]
                                    .contains_key(&validator.clone())
                            } else {
                                false
                            }
                        })
                        .collect(),
                )
            })
            .collect();

        fn bron_kerbosch<V: validator::ValidatorName>(
            r: HashSet<&V>,
            p: HashSet<&V>,
            x: HashSet<&V>,
            mx_clqs: &mut HashSet<BTreeSet<V>>,
            neighbours: HashMap<&V, HashSet<&V>>,
        ) {
            if p.is_empty() && x.is_empty() {
                let rnew: BTreeSet<V> = r.into_iter().cloned().collect();
                mx_clqs.insert(rnew);
            } else {
                let piter = p.clone();
                let mut p = p;
                let mut x = x;
                piter.into_iter().for_each(|i| {
                    p.remove(i);
                    let mut rnew = r.clone();
                    rnew.insert(i);
                    let pnew: HashSet<&V> = p.intersection(&neighbours[i]).cloned().collect();
                    let xnew: HashSet<&V> = x.intersection(&neighbours[i]).cloned().collect();
                    x.insert(i);
                    bron_kerbosch(rnew, pnew, xnew, mx_clqs, neighbours.clone())
                })
            }
        }

        let p = neighbours
            .iter()
            .fold(HashSet::new(), |acc, (_validator, x)| {
                acc.union(x).cloned().collect()
            });

        let mut mx_clqs = HashSet::new();

        bron_kerbosch(HashSet::new(), p, HashSet::new(), &mut mx_clqs, neighbours);

        mx_clqs
            .into_iter()
            .filter(|x| {
                x.iter().fold(<U as Zero<U>>::ZERO, |acc, validator| {
                    // FIXME: U::default() or <U ...>::Zero? or U::NAN
                    acc + weights.weight(validator).unwrap_or(U::NAN)
                }) > safety_oracle_threshold
            })
            .collect()
    }

    pub fn prevblock(&self) -> Option<Self> {
        self.arc().prevblock.as_ref().cloned()
    }

    /// Parses latest_msgs to return a tuple containing:
    /// * a HashMap mapping blocks to their children;
    /// * a HashSet containing blocks with None as their prevblock (aka genesis blocks or finalized
    /// blocks);
    /// * a HashMap mapping blocks to their senders.
    pub fn parse_blockchains(
        latest_msgs: &LatestMsgsHonest<Self>,
    ) -> (
        BlocksChildrenMap<V>,
        GenesisBlocks<V>,
        BlocksValidatorsMap<V>,
    ) {
        let latest_blocks: HashMap<Block<V>, V> = latest_msgs
            .iter()
            .map(|msg| (Block::from(msg), msg.sender().clone()))
            .collect();
        // start at the tip of the blockchain
        let mut visited_parents: HashMap<Block<V>, HashSet<Block<V>>> = latest_msgs
            .iter()
            .map(|msg| {
                let parent = Block::from(msg);
                let children = HashSet::new();
                (parent, children)
            })
            .collect();

        let mut queue: VecDeque<Block<V>> = visited_parents.keys().cloned().collect();
        let mut genesis: HashSet<Block<V>> = HashSet::new();
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
                        if let Some(parents_children) = visited_parents.get_mut(&parent) {
                            parents_children.insert(child);
                        }
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
        block: &Block<V>,
        visited: &HashMap<Block<V>, HashSet<Block<V>>>,
        latest_blocks: &HashMap<Block<V>, V>,
        b_in_lms_validators: &mut HashMap<Block<V>, HashSet<V>>,
    ) -> HashSet<V> {
        let mut validators = HashSet::new();
        // collect this validator if this block is his proposed one from his latest message
        latest_blocks
            .get(block)
            .map(|validator| validators.insert(validator.clone()));
        let res = visited
            .get(block)
            .map(|children| {
                children.iter().fold(validators.clone(), |acc, child| {
                    let res = Self::collect_validators(
                        child,
                        visited,
                        latest_blocks,
                        b_in_lms_validators,
                    );
                    res.union(&acc).cloned().collect()
                })
            })
            .unwrap_or_else(|| validators);
        b_in_lms_validators.insert(block.clone(), res.clone());
        res
    }

    /// Find heaviest block.
    fn pick_heaviest<U: WeightUnit>(
        blocks: &HashSet<Block<V>>,
        visited: &HashMap<Block<V>, HashSet<Block<V>>>,
        weights: &validator::Weights<V, U>,
        latest_blocks: &HashMap<Block<V>, V>,
        b_in_lms_validators: &mut HashMap<Block<V>, HashSet<V>>,
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
                    let referred_validators = match b_in_lms_validators.get(block).cloned() {
                        Some(rs) => rs,
                        None => Self::collect_validators(
                            block,
                            visited,
                            latest_blocks,
                            b_in_lms_validators,
                        ),
                    };
                    let weight = weights.sum_weight_validators(&referred_validators);
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
                    b_in_lms_validators,
                )
            }
        })
    }

    pub fn ghost<U: WeightUnit>(
        latest_msgs: &LatestMsgsHonest<Self>,
        validators_weights: &validator::Weights<V, U>,
    ) -> Result<Self, Error> {
        let (visited, genesis, latest_blocks) = Self::parse_blockchains(latest_msgs);

        let mut b_in_lms_validators = HashMap::<Block<V>, HashSet<V>>::new();

        Block::pick_heaviest(
            &genesis,
            &visited,
            validators_weights,
            &latest_blocks,
            &mut b_in_lms_validators,
        )
        .and_then(|(opt_block, ..)| opt_block)
        .ok_or(Error)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashSet};
    use std::iter;
    use std::iter::FromIterator;

    use crate::blockchain::{Block, Message, ProtoBlock};
    use crate::justification::{Justification, LatestMsgs, LatestMsgsHonest};
    use crate::validator;

    #[test]
    fn partial_view() {
        // Test cases where not all validators see all messages.
        let (validator0, validator1, validator2, validator3, validator4) = (0, 1, 2, 3, 4);
        let (weight0, weight1, weight2, weight3, weight4) = (1.0, 1.0, 2.0, 1.0, 1.1);
        let validators_weights = validator::Weights::new(
            [
                (validator0, weight0),
                (validator1, weight1),
                (validator2, weight2),
                (validator3, weight3),
                (validator4, weight4),
            ]
            .iter()
            .cloned()
            .collect(),
        );
        let state = validator::State::new(
            validators_weights.clone(),
            0.0,  // state fault weight
            None, // latest messages
            LatestMsgs::empty(),
            1.0,            // subjective fault weight threshold
            HashSet::new(), // equivocators
        );

        let genesis_block = Block::from(ProtoBlock::new(None));
        let latest_msgs = Justification::empty();
        let genesis_block_msg = Message::new(validator0, latest_msgs, genesis_block.clone());
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

        let m1 =
            Message::from_msgs(validator1, vec![&genesis_block_msg], &mut state.clone()).unwrap();
        // (s0, w=1.0)   gen
        // (s1, w=1.0)     \--m1
        // (s2, w=2.0)
        // (s3, w=1.0)
        // (s4, w=1.1)

        let m2 =
            Message::from_msgs(validator2, vec![&genesis_block_msg], &mut state.clone()).unwrap();
        // (s0, w=1.0)   gen
        // (s1, w=1.0)    |\--m1
        // (s2, w=2.0)    \---m2
        // (s3, w=1.0)
        // (s4, w=1.1)

        let m3 = Message::from_msgs(validator3, vec![&m1, &m2], &mut state.clone()).unwrap();
        // (s0, w=1.0)   gen
        // (s1, w=1.0)    |\--m1
        // (s2, w=2.0)    \---m2
        // (s3, w=1.0)         \---m3
        // (s4, w=1.1)

        assert_eq!(
            m3.estimate(),
            &Block::new(Some(Block::from(&m2))),
            "should build on top of m2 as validator2 has more weight"
        );

        let m4 = Message::from_msgs(validator4, vec![&m1], &mut state.clone()).unwrap();
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

        let m5 = Message::from_msgs(validator0, vec![&m3, &m2], &mut state.clone()).unwrap();
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
        let (validatorg, validator0, validator1, validator2, validator3, validator4, validator5) =
            (0, 1, 2, 3, 4, 5, 6);
        let (weightg, weight0, weight1, weight2, weight3, weight4, weight5) =
            (1.0, 1.0, 1.0, 1.0, 1.0, 1.1, 1.0);

        let validators_weights = validator::Weights::new(
            [
                (validatorg, weightg),
                (validator0, weight0),
                (validator1, weight1),
                (validator2, weight2),
                (validator3, weight3),
                (validator4, weight4),
                (validator5, weight5),
            ]
            .iter()
            .cloned()
            .collect(),
        );

        let state = validator::State::new(
            validators_weights.clone(),
            0.0,  // state fault weight
            None, // latest messages
            LatestMsgs::empty(),
            1.0,            // subjective fault weight threshold
            HashSet::new(), // equivocators
        );

        let genesis_block = Block::from(ProtoBlock::new(None));
        let latest_msgs = Justification::empty();
        let genesis_block_msg = Message::new(validatorg, latest_msgs, genesis_block.clone());
        // (sg, w=1.0)   gen
        // (s0, w=1.0)
        // (s1, w=1.0)
        // (s2, w=1.0)
        // (s3, w=1.0)
        // (s4, w=1.1)
        // (s5, w=1.0)

        let m0 =
            Message::from_msgs(validator0, vec![&genesis_block_msg], &mut state.clone()).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)     \--m0
        // (s1, w=1.0)
        // (s2, w=1.0)
        // (s3, w=1.0)
        // (s4, w=1.1)
        // (s5, w=1.0)

        let m1 = Message::from_msgs(validator1, vec![&m0], &mut state.clone()).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)     \--m0
        // (s1, w=1.0)         \--m1
        // (s2, w=1.0)
        // (s3, w=1.0)
        // (s4, w=1.1)
        // (s5, w=1.0)

        let m2 =
            Message::from_msgs(validator2, vec![&genesis_block_msg], &mut state.clone()).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)    |\--m0
        // (s1, w=1.0)    |    \--m1
        // (s2, w=1.0)    \-----------m2
        // (s3, w=1.0)
        // (s4, w=1.1)
        // (s5, w=1.0)

        let m3 = Message::from_msgs(validator3, vec![&m2], &mut state.clone()).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)    |\--m0
        // (s1, w=1.0)    |    \--m1
        // (s2, w=1.0)    \-----------m2
        // (s3, w=1.0)                 \--m3
        // (s4, w=1.1)
        // (s5, w=1.0)

        let m4 = Message::from_msgs(validator4, vec![&m2], &mut state.clone()).unwrap();
        // (sg, w=1.0)   gen
        // (s0, w=1.0)    |\--m0
        // (s1, w=1.0)    |    \--m1
        // (s2, w=1.0)    \-----------m2
        // (s3, w=1.0)                |\--m3
        // (s4, w=1.1)                \-------m4
        // (s5, w=1.0)

        let m5 = Message::from_msgs(
            validator5,
            vec![&m0, &m1, &m2, &m3, &m4],
            &mut state.clone(),
        )
        .unwrap();
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
        let validators: Vec<u32> = (0..nodes).collect();
        let weights: Vec<f64> = iter::repeat(1.0).take(nodes as usize).collect();

        let validators_weights = validator::Weights::new(
            validators
                .iter()
                .cloned()
                .zip(weights.iter().cloned())
                .collect(),
        );

        let mut state = validator::State::new(
            validators_weights.clone(),
            0.0,  // state fault weight
            None, // latest messages
            LatestMsgs::empty(),
            1.0,            // subjective fault weight threshold
            HashSet::new(), // equivocators
        );

        // block dag
        let proto_b0 = Block::from(ProtoBlock::new(None));
        let latest_msgs = Justification::empty();
        let m0 = Message::new(validators[0], latest_msgs, proto_b0.clone());

        let proto_b1 = Block::new(Some(proto_b0.clone()));
        let m1 = Message::from_msgs(validators[1], vec![&m0], &mut state).unwrap();

        let proto_b2 = Block::new(Some(proto_b1.clone()));
        let m2 = Message::from_msgs(validators[0], vec![&m1], &mut state).unwrap();

        // no clique yet, since validators[1] has not seen validators[0] seeing validators[1] having
        // proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                2.0,
                &validators_weights
            ),
            HashSet::new()
        );

        let m3 = Message::from_msgs(validators[1], vec![&m2], &mut state).unwrap();

        // clique, since both validators have seen each other having proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                validators[0],
                validators[1]
            ])])
        );

        let m4 = Message::from_msgs(validators[2], vec![&m3], &mut state).unwrap();

        let m5 = Message::from_msgs(validators[1], vec![&m4], &mut state).unwrap();

        // no second clique yet, since validators[2] has not seen validators[1] seeing validators[2] having
        // proto_b0.clone() in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                validators[0],
                validators[1]
            ])])
        );

        let m6 = Message::from_msgs(validators[2], vec![&m5], &mut state).unwrap();

        // have two cliques on proto_b0 now
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![
                BTreeSet::from_iter(vec![validators[0], validators[1]]),
                BTreeSet::from_iter(vec![validators[1], validators[2]]),
            ])
        );
        // also have two cliques on proto_b1
        assert_eq!(
            Block::safety_oracles(
                proto_b1.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![
                BTreeSet::from_iter(vec![validators[0], validators[1]]),
                BTreeSet::from_iter(vec![validators[1], validators[2]]),
            ])
        );
        // on proto_b2, only have clique {1, 2}
        assert_eq!(
            Block::safety_oracles(
                proto_b2.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                validators[1],
                validators[2]
            ])])
        );

        let m7 = Message::from_msgs(validators[0], vec![&m6], &mut state).unwrap();

        let m8 = Message::from_msgs(validators[2], vec![&m7], &mut state).unwrap();

        let _ = Message::from_msgs(validators[0], vec![&m8], &mut state).unwrap();

        // now entire network is clique
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                validators[0],
                validators[1],
                validators[2],
            ])])
        );
        assert_eq!(
            Block::safety_oracles(
                proto_b2.clone(),
                &LatestMsgsHonest::from_latest_msgs(state.latests_msgs(), state.equivocators()),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                validators[0],
                validators[1],
                validators[2],
            ])])
        );
    }
}
