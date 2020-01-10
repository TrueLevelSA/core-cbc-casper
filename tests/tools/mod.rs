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

use std::fmt;

use casper::blockchain::Block;
use casper::estimator::Estimator;
use casper::justification::LatestMessagesHonest;
use casper::validator;

use casper::ValidatorNameBlockData;

pub struct ChainData {
    pub chain_id: u32,
    pub nb_nodes: u32,
    pub node_id: u32,
    pub consensus_height: i64,
    pub longest_chain: u32,
    pub nb_messages: usize,
}

impl fmt::Display for ChainData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{};{};{};{};{};{}",
            self.chain_id,
            self.nb_nodes,
            self.node_id,
            self.consensus_height,
            self.longest_chain,
            self.nb_messages
        )
    }
}

impl ChainData {
    pub fn new(
        chain_id: u32,
        nb_nodes: u32,
        node_id: u32,
        consensus_height: i64,
        longest_chain: u32,
        nb_messages: usize,
    ) -> ChainData {
        ChainData {
            chain_id,
            nb_nodes,
            node_id,
            consensus_height,
            longest_chain,
            nb_messages,
        }
    }
}

/// Returns the height of the GHOST-selected chain.
pub fn get_height_selected_chain(
    latest_messages_honest: &LatestMessagesHonest<Block<ValidatorNameBlockData<u32>>>,
    validator_state: &validator::State<Block<ValidatorNameBlockData<u32>>, f64>,
) -> u32 {
    let selected_block = Block::estimate(
        &latest_messages_honest,
        validator_state.validators_weights(),
    )
    .unwrap()
    .prevblock()
    .ok_or(casper::blockchain::Error);
    fn reduce(block: &Block<ValidatorNameBlockData<u32>>, i: u32) -> u32 {
        match block.prevblock() {
            Some(previous_block) => reduce(&previous_block, i + 1),
            None => i,
        }
    }
    match selected_block {
        Ok(block) => reduce(&block, 1),
        _ => 0,
    }
}
