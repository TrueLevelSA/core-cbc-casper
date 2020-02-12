// Core CBC Casper
// Copyright (C) 2018 - 2020  Coordination Technology Ltd.
// Authors: pZ4 <pz4@protonmail.ch>,
//          Lederstrumpf,
//          h4sh3d <h4sh3d@truelevel.io>
//          roflolilolmao <q@truelevel.ch>
//
// This file is part of Core CBC Casper.
//
// Core CBC Casper is free software: you can redistribute it and/or modify it under the terms
// of the GNU Affero General Public License as published by the Free Software Foundation, either
// version 3 of the License, or (at your option) any later version.
//
// Core CBC Casper is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
// PURPOSE. See the GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License along with the Core CBC
// Rust Library. If not, see <https://www.gnu.org/licenses/>.

use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::convert::From;
use std::iter::Iterator;
use std::sync::Arc;

use serde_derive::Serialize;

use crate::estimator::Estimator;
use crate::justification::{Justification, LatestMessages, LatestMessagesHonest};
use crate::message::Message;
use crate::util::hash::Hash;
use crate::util::id::Id;
use crate::util::weight::{WeightUnit, Zero};
use crate::validator;

pub trait BlockData:
    std::hash::Hash + Clone + Eq + Send + Sync + Default + serde::Serialize
{
    type ValidatorName: validator::ValidatorName;

    fn validator_name(&self) -> &Self::ValidatorName;
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, Serialize)]
struct ProtoBlock<D: BlockData> {
    prevblock: Option<Block<D>>,
    data: D,
}

impl<D: BlockData> ProtoBlock<D> {
    pub fn new(prevblock: Option<Block<D>>, data: D) -> ProtoBlock<D> {
        ProtoBlock { prevblock, data }
    }
}

/// Simplest structure of a block with a `prevblock` pointer for running Casper on a blockchain.
#[derive(Clone, Eq)]
pub struct Block<D: BlockData>(Arc<ProtoBlock<D>>);

impl<D: BlockData> std::fmt::Debug for Block<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{:?} -> {:?}",
            self.id(),
            self.prevblock()
                .as_ref()
                .map(|previous_block| previous_block.id())
                .unwrap_or_default()
        )
    }
}

impl<D: BlockData> serde::Serialize for Block<D> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut message = serializer.serialize_struct("Block", 1)?;
        message.serialize_field("prevblock", &self.prevblock())?;
        message.serialize_field("data", &self.data())?;
        message.end()
    }
}

impl<D: BlockData> Id for Block<D> {
    type ID = Hash;
}

impl<D: BlockData> std::hash::Hash for Block<D> {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        self.0.hash(hasher);
    }
}

impl<D: BlockData> PartialEq for Block<D> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(self.arc(), other.arc()) || self.id() == other.id()
    }
}

impl<D: BlockData> From<ProtoBlock<D>> for Block<D> {
    fn from(protoblock: ProtoBlock<D>) -> Self {
        Block(Arc::new(protoblock))
    }
}

impl<D: BlockData> From<&Message<Block<D>>> for Block<D> {
    fn from(message: &Message<Block<D>>) -> Self {
        message.estimate().clone()
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

impl<D: BlockData> Estimator for Block<D> {
    type Error = Error;
    type ValidatorName = D::ValidatorName;

    fn estimate<U: WeightUnit>(
        latest_messages: &LatestMessagesHonest<Self>,
        validators_weights: &validator::Weights<D::ValidatorName, U>,
    ) -> Result<Self, Self::Error> {
        let prevblock = Block::optimized_ghost(latest_messages, validators_weights)?;
        Ok(Block::from(ProtoBlock::new(Some(prevblock), D::default())))
    }
}

type BlocksChildrenMap<D> = HashMap<Block<D>, HashSet<Block<D>>>;
type GenesisBlocks<D> = HashSet<Block<D>>;
type BlocksValidatorsMap<D> = HashMap<Block<D>, <D as BlockData>::ValidatorName>;

impl<D: BlockData> Block<D> {
    pub fn new(prevblock: Option<Block<D>>, data: D) -> Self {
        Block::from(ProtoBlock::new(prevblock, data))
    }

    fn arc(&self) -> &Arc<ProtoBlock<D>> {
        &self.0
    }

    /// Creates a new block from a prevblock message and an incomplete block.
    /// An incomplete_block is a block with a None prevblock (i.e., Estimator) AND is not a
    /// genesis_block
    pub fn from_prevblock_message(
        prevblock_message: Option<Message<Block<D>>>,
        incomplete_block: Block<D>,
    ) -> Self {
        let prevblock = prevblock_message.map(|message| Block::from(&message));
        Block::from(ProtoBlock {
            prevblock,
            ..((**incomplete_block.arc()).clone())
        })
    }

    /// Mathematical definition of blockchain membership.
    pub fn is_member(&self, other: &Self) -> bool {
        self == other
            || other
                .prevblock()
                .as_ref()
                .map(|prevblock| self.is_member(prevblock))
                .unwrap_or(false)
    }

    /// Direct implementation of the score function from the paper. Contrary to the paper's
    /// definition, score directly uses the latest honest messages rather than the latest honest
    /// estimates and a protocol state. Source:
    /// https://github.com/cbc-casper/cbc-casper-paper/blob/acc66e2ba4461a005262e2d5f434fd2e30ef0ff3/examples.tex#L568
    pub fn score<U: WeightUnit>(
        &self,
        latest_messages_honest: &LatestMessagesHonest<Self>,
        weights: &validator::Weights<D::ValidatorName, U>,
    ) -> U {
        latest_messages_honest
            .iter()
            .filter(|message| self.is_member(&message.estimate()))
            .fold(<U as Zero<U>>::ZERO, |acc, message| {
                match weights.weight(&message.sender()) {
                    Err(_) => acc,
                    Ok(weight) => acc + weight,
                }
            })
    }

    /// Direct implementation of the children function from the paper. Contrary to the paper's
    /// definition, we are directly parsing blocks to filter children out of rather than taking
    /// the estimates out of messages. Source:
    /// https://github.com/cbc-casper/cbc-casper-paper/blob/acc66e2ba4461a005262e2d5f434fd2e30ef0ff3/examples.tex#L578
    pub fn children<'z>(&self, protocol_state: &HashSet<&'z Self>) -> HashSet<&'z Self> {
        protocol_state
            .iter()
            .cloned()
            .filter(|block| block.prevblock() == Some(self.clone()))
            .collect()
    }

    /// Direct implementation of the argmax function from the paper. Source:
    /// https://github.com/cbc-casper/cbc-casper-paper/blob/acc66e2ba4461a005262e2d5f434fd2e30ef0ff3/examples.tex#L395
    fn argmax<'z, F, U>(items: HashSet<&'z Block<D>>, scoring_function: F) -> HashSet<&'z Block<D>>
    where
        F: std::ops::Fn(&Block<D>) -> U,
        U: WeightUnit + std::cmp::PartialOrd,
    {
        let mut iterator = items.iter();

        let item = iterator.next();
        if item == None {
            return HashSet::new();
        }

        let item = item.unwrap();

        let mut max_score = scoring_function(item);
        let mut max = HashSet::new();
        max.insert(*item);

        for item in iterator {
            let block_score = scoring_function(*item);

            match block_score.partial_cmp(&max_score) {
                Some(Ordering::Equal) => {
                    max.insert(*item);
                }
                Some(Ordering::Greater) => max.clear(),
                Some(Ordering::Less) | None => (),
            };

            if max.is_empty() {
                max.insert(*item);
                max_score = block_score;
            }
        }

        max
    }

    /// Direct implementation of the best children function from the paper. Source:
    /// https://github.com/cbc-casper/cbc-casper-paper/blob/acc66e2ba4461a005262e2d5f434fd2e30ef0ff3/examples.tex#L587
    pub fn best_children<'z, U: WeightUnit + std::cmp::PartialOrd>(
        &self,
        protocol_state: &HashSet<&'z Self>,
        latest_messages_honest: &LatestMessagesHonest<Self>,
        weights: &validator::Weights<D::ValidatorName, U>,
    ) -> HashSet<&'z Self> {
        let scoring_function = |block: &Self| block.score(latest_messages_honest, weights);
        Block::argmax(self.children(&protocol_state), &scoring_function)
    }

    /// This function reconstructs the blocks tree from `latest_messages_honest` and uses those to
    /// return the block with highest score according to the definition 4.30 of the paper. Contrary
    /// to the paper's definition, it does not return a set in case of a tie but uses the blocks
    /// hashes to tie break. Source:
    /// https://github.com/cbc-casper/cbc-casper-paper/blob/acc66e2ba4461a005262e2d5f434fd2e30ef0ff3/examples.tex#L596
    pub fn mathematical_ghost<U: WeightUnit + std::cmp::PartialOrd>(
        latest_messages_honest: &LatestMessagesHonest<Self>,
        weights: &validator::Weights<D::ValidatorName, U>,
    ) -> Result<Self, Error> {
        fn internal<'z, D, U, F>(
            blocks: HashSet<&'z Block<D>>,
            protocol_state: &HashSet<&'z Block<D>>,
            scoring_function: F,
        ) -> HashSet<&'z Block<D>>
        where
            D: BlockData,
            U: WeightUnit + std::cmp::PartialOrd,
            F: std::ops::Fn(&Block<D>) -> U + Copy,
        {
            let children: HashMap<&Block<D>, HashSet<&Block<D>>> = blocks
                .iter()
                .map(|block| (*block, block.children(&protocol_state)))
                .collect();

            let mut indirect_best_leaves = HashSet::new();
            let mut direct_child_leaves = HashSet::new();

            for block in blocks.iter() {
                if children.get(*block).unwrap().is_empty() {
                    direct_child_leaves.insert(*block);
                } else {
                    internal(
                        Block::argmax(
                            children.get(*block).unwrap().iter().cloned().collect(),
                            scoring_function,
                        ),
                        protocol_state,
                        scoring_function,
                    )
                    .into_iter()
                    .for_each(|block| {
                        indirect_best_leaves.insert(block);
                    });
                }
            }

            indirect_best_leaves
                .union(&direct_child_leaves)
                .cloned()
                .collect()
        }

        let scoring_function = |block: &Self| block.score(latest_messages_honest, weights);

        let protocol_state = Self::find_all_accessible_blocks(latest_messages_honest);
        let genesis_blocks = protocol_state
            .iter()
            .filter(|block| block.prev_block_as_ref().is_none())
            .collect();

        // Tie breaker uses the blocks hashes.
        internal(
            genesis_blocks,
            &protocol_state.iter().collect(),
            scoring_function,
        )
        .into_iter()
        .max_by(|left, right| right.id().cmp(&left.id()))
        .cloned()
        .ok_or(Error)
    }

    /// This function reconstructs the blocks tree from `latest_messages_honest` and uses those to
    /// return the block with highest score according to the definition 4.30 of the paper. Contrary
    /// to the paper's definition, it does not return a set in case of a tie but uses the blocks
    /// hashes to tie break. It is an optimized version of `mathematical_ghost`.
    pub fn optimized_ghost<U: WeightUnit + std::cmp::PartialOrd>(
        latest_messages_honest: &LatestMessagesHonest<Self>,
        weights: &validator::Weights<D::ValidatorName, U>,
    ) -> Result<Self, Error> {
        let protocol_state = Self::find_all_accessible_blocks(latest_messages_honest);
        let genesis_blocks: HashSet<&Block<D>> = protocol_state
            .iter()
            .filter(|block| block.prev_block_as_ref().is_none())
            .collect();

        // Generating a hashset for each block containing each latest honest message child of
        // that block. This will let us compute the scores of each block easily since the score is
        // the sum of the validators having a latest message child of that block.
        let mut latest_messages_validators = HashMap::new();
        for message in latest_messages_honest.iter() {
            let mut iterator = message.estimate().clone();
            while let Some(prev_block) = iterator.prevblock() {
                let entry = latest_messages_validators
                    .entry(iterator)
                    .or_insert_with(HashSet::new);
                entry.insert(message.sender().clone());

                iterator = prev_block;
            }
            let entry = latest_messages_validators
                .entry(iterator)
                .or_insert_with(HashSet::new);
            entry.insert(message.sender().clone());
        }

        let scores: HashMap<&Block<D>, U> = latest_messages_validators
            .iter()
            .map(|(block, validators)| {
                (
                    protocol_state.get(block).unwrap(),
                    weights.sum_weight_validators(&validators),
                )
            })
            .collect();

        let scoring_function = |block: &Self| *scores.get(&block).unwrap();

        let mut stack = vec![genesis_blocks.into_iter().next().unwrap()];
        let mut result = HashSet::new();

        // This while loop is an iterative ghost.
        while let Some(block) = stack.pop() {
            let children = block.children(&protocol_state.iter().collect());

            if children.is_empty() {
                result.insert(block.clone());
            } else {
                Block::argmax(children, scoring_function)
                    .into_iter()
                    .for_each(|block| {
                        stack.push(block);
                    });
            }
        }

        // Tie breaker uses the blocks hashes.
        result
            .into_iter()
            .max_by(|left, right| right.id().cmp(&left.id()))
            .ok_or(Error)
    }

    pub fn safety_oracles<U: WeightUnit>(
        block: Block<D>,
        latest_messages_honest: &LatestMessagesHonest<Self>,
        equivocators: &HashSet<D::ValidatorName>,
        safety_oracle_threshold: U,
        weights: &validator::Weights<D::ValidatorName, U>,
    ) -> HashSet<BTreeSet<D::ValidatorName>> {
        fn latest_in_justification<D: BlockData>(
            justification: &Justification<Block<D>>,
            equivocators: &HashSet<D::ValidatorName>,
        ) -> HashMap<D::ValidatorName, Message<Block<D>>> {
            LatestMessagesHonest::from_latest_messages(
                &LatestMessages::from(justification),
                equivocators,
            )
            .iter()
            .map(|message| (message.sender().clone(), message.clone()))
            .collect()
        }

        let latest_containing_block: HashSet<&Message<Block<D>>> = latest_messages_honest
            .iter()
            .filter(|&message| block.is_member(&Block::from(message)))
            .collect();

        let latest_agreeing_in_validator_view: HashMap<_, HashMap<_, Message<Block<D>>>> =
            latest_containing_block
                .iter()
                .map(|message| {
                    (
                        message.sender().clone(),
                        latest_in_justification(message.justification(), equivocators)
                            .into_iter()
                            .filter(|(_validator, message)| block.is_member(&Block::from(message)))
                            .collect(),
                    )
                })
                .collect();

        let neighbours: HashMap<&D::ValidatorName, HashSet<&D::ValidatorName>> =
            latest_agreeing_in_validator_view
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

        fn bron_kerbosch<D: BlockData>(
            r: HashSet<&D::ValidatorName>,
            p: HashSet<&D::ValidatorName>,
            x: HashSet<&D::ValidatorName>,
            mx_clqs: &mut HashSet<BTreeSet<D::ValidatorName>>,
            neighbours: HashMap<&D::ValidatorName, HashSet<&D::ValidatorName>>,
        ) {
            if p.is_empty() && x.is_empty() {
                let rnew: BTreeSet<D::ValidatorName> = r.into_iter().cloned().collect();
                mx_clqs.insert(rnew);
            } else {
                let piter = p.clone();
                let mut p = p;
                let mut x = x;
                piter.into_iter().for_each(|i| {
                    p.remove(i);
                    let mut rnew = r.clone();
                    rnew.insert(i);
                    let pnew: HashSet<&D::ValidatorName> =
                        p.intersection(&neighbours[i]).cloned().collect();
                    let xnew: HashSet<&D::ValidatorName> =
                        x.intersection(&neighbours[i]).cloned().collect();
                    x.insert(i);
                    bron_kerbosch::<D>(rnew, pnew, xnew, mx_clqs, neighbours.clone())
                })
            }
        }

        let p = neighbours
            .iter()
            .fold(HashSet::new(), |acc, (_validator, x)| {
                acc.union(x).cloned().collect()
            });

        let mut mx_clqs = HashSet::new();

        bron_kerbosch::<D>(HashSet::new(), p, HashSet::new(), &mut mx_clqs, neighbours);

        mx_clqs
            .into_iter()
            .filter(|x| {
                x.iter().fold(<U as Zero<U>>::ZERO, |acc, validator| {
                    // Having a non existing validator would be a fault we can not recover from
                    // since we cannot know or invent the weight of an arbitrary validator.
                    acc + weights.weight(validator).unwrap()
                }) > safety_oracle_threshold
            })
            .collect()
    }

    /// Contrary to the paper's definition 4.24, this does not return Self for a genesis block but
    /// None. Source:
    /// https://github.com/cbc-casper/cbc-casper-paper/blob/acc66e2ba4461a005262e2d5f434fd2e30ef0ff3/examples.tex#L525
    pub fn prevblock(&self) -> Option<Self> {
        self.arc().prevblock.as_ref().cloned()
    }

    pub fn prev_block_as_ref(&self) -> Option<&Self> {
        self.arc().prevblock.as_ref()
    }

    pub fn data(&self) -> D {
        self.arc().data.clone()
    }

    /// Contrary to the paper's definition 4.25, this does not return Self for a genesis block but
    /// None. Source:
    /// https://github.com/cbc-casper/cbc-casper-paper/blob/acc66e2ba4461a005262e2d5f434fd2e30ef0ff3/examples.tex#L544
    pub fn ncestor(&self, n: u32) -> Option<Self> {
        if n == 0 {
            return Some(self.clone());
        }

        match self.prevblock() {
            Some(block) => Block::ncestor(&block, n - 1),
            None => None,
        }
    }

    /// Parses latest_messages to return a tuple containing:
    /// * a HashMap mapping blocks to their children;
    /// * a HashSet containing blocks with None as their prevblock (aka genesis blocks or finalized
    /// blocks);
    /// * a HashMap mapping blocks to their senders.
    pub fn parse_blockchains(
        latest_messages: &LatestMessagesHonest<Self>,
    ) -> (
        BlocksChildrenMap<D>,
        GenesisBlocks<D>,
        BlocksValidatorsMap<D>,
    ) {
        let latest_blocks: HashMap<Block<D>, D::ValidatorName> = latest_messages
            .iter()
            .map(|message| (Block::from(message), message.sender().clone()))
            .collect();
        // start at the tip of the blockchain
        let mut visited_parents: HashMap<Block<D>, HashSet<Block<D>>> = latest_messages
            .iter()
            .map(|message| {
                let parent = Block::from(message);
                let children = HashSet::new();
                (parent, children)
            })
            .collect();

        let mut queue: VecDeque<Block<D>> = visited_parents.keys().cloned().collect();
        let mut genesis: HashSet<Block<D>> = HashSet::new();
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

    pub fn find_all_accessible_blocks(
        latest_messages: &LatestMessagesHonest<Self>,
    ) -> HashSet<Block<D>> {
        let mut blocks = HashSet::new();

        for message in latest_messages.iter() {
            let mut block = message.estimate().clone();

            while let Some(prev_block) = block.prevblock() {
                if blocks.contains(&block) {
                    break;
                }

                blocks.insert(block);
                block = prev_block.clone();
            }

            blocks.insert(block);
        }

        blocks
    }

    /// Collects the validators that produced blocks for each side of a fork.
    fn collect_validators(
        block: &Block<D>,
        visited: &HashMap<Block<D>, HashSet<Block<D>>>,
        latest_blocks: &HashMap<Block<D>, D::ValidatorName>,
        b_in_lms_validators: &mut HashMap<Block<D>, HashSet<D::ValidatorName>>,
    ) -> HashSet<D::ValidatorName> {
        let mut validators = HashSet::new();
        // Collect this validator if this block is his proposed one from his latest message.
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
        blocks: &HashSet<Block<D>>,
        visited: &HashMap<Block<D>, HashSet<Block<D>>>,
        weights: &validator::Weights<D::ValidatorName, U>,
        latest_blocks: &HashMap<Block<D>, D::ValidatorName>,
        b_in_lms_validators: &mut HashMap<Block<D>, HashSet<D::ValidatorName>>,
    ) -> Option<(Option<Self>, U, HashSet<Self>)> {
        let init = Some((None, <U as Zero<U>>::ZERO, HashSet::new()));
        let heaviest_child = match blocks.len() {
            // only one choice, no need to compute anything
            length if length == 1 => blocks.iter().next().cloned().and_then(|block| {
                visited
                    .get(&block)
                    .map(|children| (Some(block), <U as Zero<U>>::ZERO, children.clone()))
            }),
            // fork, need to find best block
            length if length > 1 => blocks.iter().fold(init, |best, block| {
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
                    match weight.partial_cmp(&b_weight) {
                        Some(Ordering::Greater) => res,
                        Some(Ordering::Less) => b_res,
                        Some(Ordering::Equal) | None => {
                            // break ties with blockhash
                            let ord = b_block.as_ref().map(|b| b.id().cmp(&block.id()));
                            match ord {
                                Some(Ordering::Greater) => res,
                                Some(Ordering::Less) => b_res,
                                Some(Ordering::Equal) => b_res,
                                None => None,
                            }
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

    pub fn old_ghost<U: WeightUnit>(
        latest_messages: &LatestMessagesHonest<Self>,
        validators_weights: &validator::Weights<D::ValidatorName, U>,
    ) -> Result<Self, Error> {
        let (visited, genesis, latest_blocks) = Self::parse_blockchains(latest_messages);

        let mut b_in_lms_validators = HashMap::<Block<D>, HashSet<D::ValidatorName>>::new();

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
    use super::*;

    use std::collections::{BTreeSet, HashSet};
    use std::iter;
    use std::iter::FromIterator;

    use crate::justification::{Justification, LatestMessages, LatestMessagesHonest};
    use crate::validator;

    use crate::ValidatorNameBlockData;

    #[test]
    fn ncestor() {
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        let block_1 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(3));
        let block_2 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(5));

        assert_eq!(genesis.ncestor(0), Some(genesis.clone()));
        assert_eq!(genesis.ncestor(1), None);

        assert_eq!(block_2.ncestor(0), Some(block_2.clone()));
        assert_eq!(block_2.ncestor(1), Some(block_1));
        assert_eq!(block_2.ncestor(2), Some(genesis));
        assert_eq!(block_2.ncestor(3), None);
    }

    #[test]
    fn from_prevblock_message() {
        let incomplete_block = Block::new(None, ValidatorNameBlockData::new(0));
        let message = Message::new(
            1,
            Justification::empty(),
            Block::from(ProtoBlock::new(None, ValidatorNameBlockData::new(2))),
        );

        assert_eq!(
            Block::from_prevblock_message(Some(message.clone()), incomplete_block),
            Block::new(Some(Block::from(&message)), ValidatorNameBlockData::new(0)),
        );
    }

    #[test]
    fn from_prevblock_message_none() {
        let incomplete_block = Block::new(None, ValidatorNameBlockData::new(0));

        assert_eq!(
            Block::from_prevblock_message(None, incomplete_block),
            Block::new(None, ValidatorNameBlockData::new(0)),
        );
    }

    #[test]
    fn is_member_self() {
        let block = Block::new(
            Some(Block::from(&Message::new(
                0,
                Justification::empty(),
                Block::new(None, ValidatorNameBlockData::new(1)),
            ))),
            ValidatorNameBlockData::new(2),
        );
        assert!(block.is_member(&block));
        assert!(Block::new(None, ValidatorNameBlockData::new(0))
            .is_member(&Block::new(None, ValidatorNameBlockData::new(0))));
        assert!(!Block::new(None, ValidatorNameBlockData::new(0))
            .is_member(&Block::new(None, ValidatorNameBlockData::new(1))));
    }

    #[test]
    fn is_member_ancestor() {
        let message = Message::new(
            0,
            Justification::empty(),
            Block::new(None, ValidatorNameBlockData::new(1)),
        );
        let block_1 = Block::from(&message);
        let block_2 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(2));

        assert!(block_1.is_member(&block_2));
        assert!(Block::from(&message).is_member(&block_1));
        assert!(Block::from(&message).is_member(&block_2));

        assert!(!block_2.is_member(&block_1));
        assert!(!block_2.is_member(&Block::from(&message)));
    }

    #[test]
    fn score() {
        let weights = validator::Weights::new(
            vec![(0, 1.0), (1, 2.0), (2, 4.0), (3, 8.0), (4, 16.0)]
                .into_iter()
                .collect(),
        );
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        let block_1 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(1));
        let block_2 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(2));
        let block_3 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(3));
        let block_4 = Block::new(Some(block_3.clone()), ValidatorNameBlockData::new(0));
        let block_5 = Block::new(Some(block_4.clone()), ValidatorNameBlockData::new(4));

        let mut justification = Justification::empty();
        justification.insert(Message::new(0, justification.clone(), genesis.clone()));
        justification.insert(Message::new(1, justification.clone(), block_1.clone()));
        justification.insert(Message::new(2, justification.clone(), block_2.clone()));
        justification.insert(Message::new(3, justification.clone(), block_3.clone()));
        justification.insert(Message::new(0, justification.clone(), block_4.clone()));
        justification.insert(Message::new(4, justification.clone(), block_5.clone()));
        let latest_messages = LatestMessages::from(&justification);

        float_eq!(
            genesis.score(
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights
            ),
            31.0
        );
        float_eq!(
            block_1.score(
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights
            ),
            31.0
        );
        float_eq!(
            block_2.score(
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights
            ),
            4.0
        );
        float_eq!(
            block_3.score(
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights
            ),
            25.0
        );
        float_eq!(
            block_4.score(
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights
            ),
            17.0
        );
        float_eq!(
            block_5.score(
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights
            ),
            16.0
        );
    }

    #[test]
    fn children() {
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        let block_1 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(1));
        let block_2 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(2));
        let block_3 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(3));
        let block_4 = Block::new(Some(block_3.clone()), ValidatorNameBlockData::new(0));

        assert_eq!(
            genesis.children(
                &vec![&genesis, &block_1, &block_2, &block_3, &block_4]
                    .into_iter()
                    .collect::<HashSet<_>>()
            ),
            vec![&block_1].into_iter().collect::<HashSet<_>>()
        );
        assert_eq!(
            block_1.children(
                &vec![&genesis, &block_1, &block_2, &block_3, &block_4]
                    .into_iter()
                    .collect::<HashSet<_>>()
            ),
            vec![&block_2, &block_3].into_iter().collect::<HashSet<_>>()
        );
        assert_eq!(
            block_2.children(
                &vec![&genesis, &block_1, &block_2, &block_3, &block_4]
                    .into_iter()
                    .collect::<HashSet<_>>()
            ),
            vec![].into_iter().collect::<HashSet<_>>()
        );
        assert_eq!(
            block_3.children(
                &vec![&genesis, &block_1, &block_2, &block_3, &block_4]
                    .into_iter()
                    .collect::<HashSet<_>>()
            ),
            vec![&block_4].into_iter().collect::<HashSet<_>>()
        );
    }

    #[test]
    fn children_missing_children_are_not_included() {
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        let block_1 = Block::new(Some(genesis), ValidatorNameBlockData::new(1));
        let block_2 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(2));
        let block_3 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(3));
        let block_4 = Block::new(Some(block_3), ValidatorNameBlockData::new(0));

        assert_eq!(
            block_1.children(&vec![&block_2, &block_4].into_iter().collect::<HashSet<_>>()),
            vec![&block_2].into_iter().collect::<HashSet<_>>()
        );
    }

    #[test]
    fn best_children_trivial() {
        let weights = validator::Weights::new(
            vec![(0, 3.0), (1, 2.0), (2, 4.0), (3, 8.0), (4, 1.0)]
                .into_iter()
                .collect(),
        );
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        let block_1 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(1));
        let block_2 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(2));
        let block_3 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(3));
        let block_4 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(4));

        let mut justification = Justification::empty();
        justification.insert(Message::new(0, justification.clone(), genesis.clone()));
        justification.insert(Message::new(1, justification.clone(), block_1.clone()));
        justification.insert(Message::new(2, justification.clone(), block_2.clone()));
        justification.insert(Message::new(3, justification.clone(), block_3.clone()));
        justification.insert(Message::new(4, justification.clone(), block_4.clone()));
        let latest_messages = LatestMessages::from(&justification);

        assert_eq!(
            genesis.best_children(
                &vec![&block_1, &block_2, &block_3, &block_4]
                    .into_iter()
                    .collect::<HashSet<_>>(),
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights,
            ),
            vec![&block_3].into_iter().collect::<HashSet<_>>()
        );
    }

    #[test]
    fn best_children_indirect() {
        let weights = validator::Weights::new(
            vec![(0, 1.0), (1, 2.0), (2, 4.0), (3, 8.0), (4, 10.0)]
                .into_iter()
                .collect(),
        );
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        let block_1 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(1));
        let block_2 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(2));
        let block_3 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(3));
        let block_4 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(4));
        let block_5 = Block::new(Some(block_4.clone()), ValidatorNameBlockData::new(0));
        let block_6 = Block::new(Some(block_2.clone()), ValidatorNameBlockData::new(3));

        let mut justification = Justification::empty();
        justification.insert(Message::new(0, justification.clone(), genesis.clone()));
        justification.insert(Message::new(1, justification.clone(), block_1.clone()));
        justification.insert(Message::new(2, justification.clone(), block_2.clone()));
        justification.insert(Message::new(3, justification.clone(), block_3.clone()));
        justification.insert(Message::new(4, justification.clone(), block_4.clone()));
        justification.insert(Message::new(0, justification.clone(), block_5));
        justification.insert(Message::new(3, justification.clone(), block_6));
        let latest_messages = LatestMessages::from(&justification);

        assert_eq!(
            genesis.best_children(
                &vec![&block_1, &block_2, &block_3, &block_4]
                    .into_iter()
                    .collect::<HashSet<_>>(),
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights,
            ),
            vec![&block_2].into_iter().collect::<HashSet<_>>()
        );
    }

    #[test]
    fn best_children_tie() {
        let weights = validator::Weights::new(
            vec![(0, 1.0), (1, 2.0), (2, 4.0), (3, 8.0), (4, 10.0)]
                .into_iter()
                .collect(),
        );
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        let block_1 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(1));
        let block_2 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(2));
        let block_3 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(3));
        let block_4 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(4));
        let block_5 = Block::new(Some(block_2.clone()), ValidatorNameBlockData::new(0));
        let block_6 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(3));

        let mut justification = Justification::empty();
        justification.insert(Message::new(0, justification.clone(), genesis.clone()));
        justification.insert(Message::new(1, justification.clone(), block_1.clone()));
        justification.insert(Message::new(2, justification.clone(), block_2.clone()));
        justification.insert(Message::new(3, justification.clone(), block_3.clone()));
        justification.insert(Message::new(4, justification.clone(), block_4.clone()));
        justification.insert(Message::new(0, justification.clone(), block_5));
        justification.insert(Message::new(3, justification.clone(), block_6));
        let latest_messages = LatestMessages::from(&justification);

        assert_eq!(
            genesis.best_children(
                &vec![&block_1, &block_2, &block_3, &block_4]
                    .into_iter()
                    .collect::<HashSet<_>>(),
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights,
            ),
            vec![&block_1, &block_4].into_iter().collect::<HashSet<_>>()
        );
    }

    #[test]
    fn best_children_empty() {
        let weights = validator::Weights::new(vec![(0, 1.0)].into_iter().collect());
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        assert_eq!(
            genesis.best_children(
                &HashSet::new(),
                &LatestMessagesHonest::from_latest_messages(
                    &LatestMessages::empty(),
                    &HashSet::new()
                ),
                &weights,
            ),
            HashSet::new()
        );
    }

    #[test]
    fn ghost() {
        let weights = validator::Weights::new(
            vec![(0, 1.0), (1, 2.0), (2, 4.0), (3, 8.0), (4, 16.0)]
                .into_iter()
                .collect(),
        );
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        let block_1 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(1));
        let block_2 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(2));
        let block_3 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(3));
        let block_4 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(4));

        let block_5 = Block::new(Some(block_4.clone()), ValidatorNameBlockData::new(0));
        let block_6 = Block::new(Some(block_2.clone()), ValidatorNameBlockData::new(3));

        let block_7 = Block::new(Some(block_5.clone()), ValidatorNameBlockData::new(2));
        let block_8 = Block::new(Some(block_6.clone()), ValidatorNameBlockData::new(4));

        let mut justification = Justification::empty();
        justification.insert(Message::new(0, justification.clone(), genesis));
        justification.insert(Message::new(1, justification.clone(), block_1));
        justification.insert(Message::new(2, justification.clone(), block_2));
        justification.insert(Message::new(3, justification.clone(), block_3));
        justification.insert(Message::new(4, justification.clone(), block_4));
        justification.insert(Message::new(0, justification.clone(), block_5));
        justification.insert(Message::new(3, justification.clone(), block_6));
        justification.insert(Message::new(2, justification.clone(), block_7));
        justification.insert(Message::new(4, justification.clone(), block_8.clone()));
        let latest_messages = LatestMessages::from(&justification);

        assert_eq!(
            Block::mathematical_ghost(
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights,
            )
            .unwrap(),
            block_8,
        );
        assert_eq!(
            Block::optimized_ghost(
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights,
            )
            .unwrap(),
            block_8,
        );
        assert_eq!(
            Block::old_ghost(
                &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new()),
                &weights,
            )
            .unwrap(),
            block_8,
        );
    }

    #[test]
    fn ghost_tie() {
        let weights = validator::Weights::new(
            vec![(0, 1.0), (1, 2.0), (2, 4.0), (3, 8.0), (4, 10.0), (5, 0.0)]
                .into_iter()
                .collect(),
        );
        let genesis = Block::new(None, ValidatorNameBlockData::new(0));
        let block_1 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(1));
        let block_2 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(2));
        let block_3 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(3));
        let block_4 = Block::new(Some(genesis.clone()), ValidatorNameBlockData::new(4));
        let block_5 = Block::new(Some(block_2.clone()), ValidatorNameBlockData::new(0));
        let block_6 = Block::new(Some(block_1.clone()), ValidatorNameBlockData::new(3));
        let block_7 = Block::new(Some(block_6.clone()), ValidatorNameBlockData::new(5));

        let mut justification = Justification::empty();
        justification.insert(Message::new(0, justification.clone(), genesis));
        justification.insert(Message::new(1, justification.clone(), block_1));
        justification.insert(Message::new(2, justification.clone(), block_2));
        justification.insert(Message::new(3, justification.clone(), block_3));
        justification.insert(Message::new(4, justification.clone(), block_4.clone()));
        justification.insert(Message::new(0, justification.clone(), block_5));
        justification.insert(Message::new(3, justification.clone(), block_6));
        justification.insert(Message::new(5, justification.clone(), block_7));
        let latest_messages = LatestMessages::from(&justification);
        let latest_honest_messages =
            &LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new());

        // block_4 and block_7 are tied but the hash based tie breaker chooses block_4.
        assert_eq!(
            Block::mathematical_ghost(latest_honest_messages, &weights,).unwrap(),
            block_4,
        );
        assert_eq!(
            Block::optimized_ghost(latest_honest_messages, &weights,).unwrap(),
            block_4,
        );
        assert_eq!(
            Block::old_ghost(latest_honest_messages, &weights,).unwrap(),
            block_4,
        );
    }

    #[test]
    fn from_message() {
        let block_1 = Block::new(
            Some(Block::new(None, ValidatorNameBlockData::new(0))),
            ValidatorNameBlockData::new(1),
        );
        let message = Message::new(0, Justification::empty(), block_1.clone());
        let block_2 = Block::from(&message);

        assert_eq!(block_1, block_2);
    }

    #[test]
    fn parse_blockchains() {
        let genesis = Message::new(
            0,
            Justification::empty(),
            Block::new(None, ValidatorNameBlockData::new(0)),
        );
        let mut justification = Justification::empty();
        justification.insert(genesis.clone());
        let block_1 = Message::new(
            1,
            justification.clone(),
            Block::new(
                Some(genesis.estimate().clone()),
                ValidatorNameBlockData::new(3),
            ),
        );
        let block_2 = Message::new(
            2,
            justification,
            Block::new(
                Some(genesis.estimate().clone()),
                ValidatorNameBlockData::new(4),
            ),
        );

        let mut latest_messages = LatestMessages::empty();
        latest_messages.update(&genesis);
        latest_messages.update(&block_1);
        latest_messages.update(&block_2);
        let latest_messages_honest =
            LatestMessagesHonest::from_latest_messages(&latest_messages, &HashSet::new());

        let (children_map, genesis_set, senders_map) =
            Block::parse_blockchains(&latest_messages_honest);

        assert_eq!(
            children_map,
            vec![
                (
                    genesis.estimate().clone(),
                    HashSet::from_iter(vec![
                        block_1.estimate().clone(),
                        block_2.estimate().clone()
                    ])
                ),
                (block_1.estimate().clone(), HashSet::new()),
                (block_2.estimate().clone(), HashSet::new()),
            ]
            .into_iter()
            .collect(),
        );
        assert_eq!(
            genesis_set,
            HashSet::from_iter(vec![genesis.estimate().clone()]),
        );

        assert_eq!(
            senders_map,
            vec![
                (genesis.estimate().clone(), 0),
                (block_1.estimate().clone(), 1),
                (block_2.estimate().clone(), 2)
            ]
            .into_iter()
            .collect(),
        );
    }

    #[test]
    fn safety_oracles() {
        let nodes = 3;
        let validators: Vec<u32> = (0..nodes).collect();

        let validators_weights =
            validator::Weights::new(validators.iter().cloned().zip(iter::repeat(1.0)).collect());

        let mut state = validator::State::new(
            validators_weights.clone(),
            0.0,
            LatestMessages::empty(),
            1.0,
            HashSet::new(),
        );

        // block dag
        let proto_b0 = Block::from(ProtoBlock::new(None, ValidatorNameBlockData::new(0)));
        let latest_messages = Justification::empty();
        let m0 = Message::new(validators[0], latest_messages, proto_b0.clone());

        let proto_b1 = Block::new(Some(proto_b0.clone()), ValidatorNameBlockData::new(0));
        state.update(&[&m0]);
        let m1 = Message::from_validator_state(validators[1], &state).unwrap();

        let proto_b2 = Block::new(Some(proto_b1.clone()), ValidatorNameBlockData::new(0));
        state.update(&[&m1]);
        let m2 = Message::from_validator_state(validators[0], &state).unwrap();

        // no clique yet, since validators[1] has not seen validators[0] seeing validators[1]
        // having proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMessagesHonest::from_latest_messages(
                    state.latests_messages(),
                    state.equivocators()
                ),
                state.equivocators(),
                2.0,
                &validators_weights
            ),
            HashSet::new()
        );

        state.update(&[&m2]);
        let m3 = Message::from_validator_state(validators[1], &state).unwrap();

        // clique, since both validators have seen each other having proto_b0 in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMessagesHonest::from_latest_messages(
                    state.latests_messages(),
                    state.equivocators()
                ),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                validators[0],
                validators[1]
            ])])
        );

        state.update(&[&m3]);
        let m4 = Message::from_validator_state(validators[2], &state).unwrap();

        state.update(&[&m4]);
        let m5 = Message::from_validator_state(validators[1], &state).unwrap();

        // no second clique yet, since validators[2] has not seen validators[1] seeing
        // validators[2] having proto_b0.clone() in the chain
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMessagesHonest::from_latest_messages(
                    state.latests_messages(),
                    state.equivocators()
                ),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                validators[0],
                validators[1]
            ])])
        );

        state.update(&[&m5]);
        let m6 = Message::from_validator_state(validators[2], &state).unwrap();

        // have two cliques on proto_b0 now
        assert_eq!(
            Block::safety_oracles(
                proto_b0.clone(),
                &LatestMessagesHonest::from_latest_messages(
                    state.latests_messages(),
                    state.equivocators()
                ),
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
                proto_b1,
                &LatestMessagesHonest::from_latest_messages(
                    state.latests_messages(),
                    state.equivocators()
                ),
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
                &LatestMessagesHonest::from_latest_messages(
                    state.latests_messages(),
                    state.equivocators()
                ),
                state.equivocators(),
                1.0,
                &validators_weights
            ),
            HashSet::from_iter(vec![BTreeSet::from_iter(vec![
                validators[1],
                validators[2]
            ])])
        );

        state.update(&[&m6]);
        let m7 = Message::from_validator_state(validators[0], &state).unwrap();

        state.update(&[&m7]);
        let m8 = Message::from_validator_state(validators[2], &state).unwrap();

        state.update(&[&m8]);
        let _ = Message::from_validator_state(validators[0], &state).unwrap();

        // now entire network is clique
        assert_eq!(
            Block::safety_oracles(
                proto_b0,
                &LatestMessagesHonest::from_latest_messages(
                    state.latests_messages(),
                    state.equivocators()
                ),
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
                proto_b2,
                &LatestMessagesHonest::from_latest_messages(
                    state.latests_messages(),
                    state.equivocators()
                ),
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
