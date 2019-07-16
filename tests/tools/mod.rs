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

use std::collections::HashSet;
use std::fmt;

use casper::blockchain::{Block, Message};
use casper::justification::LatestMsgsHonest;
use casper::sender;

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

/// returns the height of the GHOST-selected chain
pub fn get_height_selected_chain(
    latest_msgs_honest: &LatestMsgsHonest<Message<u32>>,
    sender_state: &sender::State<Message<u32>, f64>,
) -> u32 {
    let selected_block = Block::ghost(&latest_msgs_honest, sender_state.senders_weights());
    fn reduce(b: &Block<u32>, i: u32) -> u32 {
        match b.prevblock() {
            Some(_msg) => reduce(&_msg, i + 1),
            None => i,
        }
    }
    let height_this_message = match selected_block {
        Ok(b) => reduce(&b, 1),
        _ => 0,
    };
    height_this_message
}

pub fn get_children_of_blocks(
    latest_msgs_honest: &LatestMsgsHonest<Message<u32>>,
    genesis_blocks: HashSet<Block<u32>>,
) -> HashSet<Block<u32>> {
    let mut children = HashSet::new();
    fn reduce(
        b: &Block<u32>,
        genesis_blocks: &HashSet<Block<u32>>,
        children: &mut HashSet<Block<u32>>,
    ) -> () {
        match b.prevblock() {
            Some(_msg) => {
                if genesis_blocks.contains(&_msg) {
                    children.insert(b.clone());
                    ()
                } else {
                    reduce(&_msg, genesis_blocks, children)
                }
            }
            _ => (),
        }
    }

    latest_msgs_honest.iter().for_each(|latest_msg| {
        let parent = Block::from(latest_msg);
        reduce(&parent, &genesis_blocks, &mut children);
    });

    children
}
