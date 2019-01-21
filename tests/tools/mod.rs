use std::fmt;
use std::collections::{HashMap, HashSet};
use casper::justification::{LatestMsgsHonest, SenderState};

use casper::example::blockchain::{Block, BlockMsg};

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

/// returns a vector of heights
/// each height is the height of the block that is selected by ghost
/// (applied to latest honest messages in each view)
pub fn heights_from_state(state: &HashMap<u32, SenderState<BlockMsg>>) -> Vec<u32> {
    state
        .iter()
        .map(|(_, sender_state)| (sender_state.latests_msgs(), sender_state.senders_weights()))
        .map(|(latest_msgs, senders_weights)| {
            let latest_messages_honest =
                LatestMsgsHonest::from_latest_msgs(latest_msgs, &HashSet::new());
            Block::ghost(&latest_messages_honest, senders_weights)
        })
        .map(|block| {
            fn reduce(b: &Block, i: u32) -> u32 {
                match b.prevblock() {
                    Some(_msg) => reduce(&_msg, i + 1),
                    None => i,
                }
            }
            let height_this_message = match block {
                Ok(b) => reduce(&b, 1),
                _ => 0,
            };
            height_this_message
        })
        .collect()
}

/// returns the height of the GHOST-selected chain
pub fn get_height_selected_chain(
    latest_msgs_honest: &LatestMsgsHonest<BlockMsg>,
    sender_state: &SenderState<BlockMsg>,
) -> u32 {
    let selected_block = Block::ghost(&latest_msgs_honest, sender_state.senders_weights());
    fn reduce(b: &Block, i: u32) -> u32 {
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
    latest_msgs_honest: &LatestMsgsHonest<BlockMsg>,
    genesis_blocks: HashSet<Block>,
) -> HashSet<Block> {
    let mut children = HashSet::new();
    fn reduce(b: &Block, genesis_blocks: &HashSet<Block>, children: &mut HashSet<Block>) -> () {
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
