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
use std::fmt::{Debug, Formatter};
use std::ops::Add;

use proptest::prelude::*;

use casper::estimator::Estimator;
use casper::justification::{Justification, LatestMsgsHonest};
use casper::message::{self, Trait};
use casper::sender;
use casper::util::weight::{WeightUnit, Zero};

#[derive(Clone, Eq, Ord, PartialOrd, PartialEq, Hash, Default, serde_derive::Serialize)]
pub struct VoteCount {
    yes: u32,
    no: u32,
}

impl<S: sender::Trait> From<S> for VoteCount {
    fn from(_sender: S) -> Self {
        VoteCount::default()
    }
}

impl Zero<VoteCount> for VoteCount {
    const ZERO: Self = Self { yes: 0, no: 0 };
}

impl Add for VoteCount {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        VoteCount {
            yes: self.yes + other.yes,
            no: self.no + other.no,
        }
    }
}

impl Debug for VoteCount {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "y{:?}/n{:?}", self.yes, self.no)
    }
}

impl VoteCount {
    pub fn arbitrary() -> BoxedStrategy<Self> {
        prop::sample::select(vec![
            VoteCount { yes: 1, no: 0 },
            VoteCount { yes: 0, no: 1 },
        ])
        .boxed()
    }
    // makes sure nobody adds more than one vote to their unjustified VoteCount
    // object. if they did, their vote is invalid and will be ignored
    fn is_valid_vote(vote: &Self) -> bool {
        // these two are the only allowed votes (unjustified msgs)
        match vote {
            VoteCount { yes: 1, no: 0 } => true,
            VoteCount { yes: 0, no: 1 } => true,
            _ => false,
        }
    }

    // used to create an equivocation vote
    fn toggle_vote(vote: &Self) -> Self {
        // these two are the only allowed votes (unjustified msgs)
        match vote {
            VoteCount { yes: 1, no: 0 } => VoteCount { yes: 0, no: 1 },
            VoteCount { yes: 0, no: 1 } => VoteCount { yes: 1, no: 0 },
            _ => VoteCount::ZERO,
        }
    }

    /// Creates a new empty vote message, issued by the sender
    /// with no justification
    pub fn create_vote_msg(sender: u32, vote: bool) -> message::Message<Self, u32> {
        let justification = Justification::empty();
        let estimate = match vote {
            true => VoteCount { yes: 1, no: 0 },
            false => VoteCount { yes: 0, no: 1 },
        };

        message::Message::new(sender, justification, estimate)
    }

    fn get_vote_msgs(
        latest_msgs: &LatestMsgsHonest<message::Message<Self, Voter>>,
    ) -> HashSet<message::Message<Self, Voter>> {
        fn recursor(
            latest_msgs: &Justification<message::Message<VoteCount, Voter>>,
            acc: HashSet<message::Message<VoteCount, Voter>>,
        ) -> HashSet<message::Message<VoteCount, Voter>> {
            latest_msgs.iter().fold(acc, |mut acc_prime, m| {
                match m.justification().len() {
                    0 => {
                        // vote found, vote is a message with 0 justification
                        let estimate = m.estimate().clone();
                        if VoteCount::is_valid_vote(&estimate) {
                            let equivocation = message::Message::new(
                                m.sender().clone(),
                                m.justification().clone(),
                                VoteCount::toggle_vote(&estimate),
                            );
                            // search for the equivocation of the current latest_msgs
                            match acc_prime.get(&equivocation) {
                                // remove the equivoted vote, none of the pair
                                // will stay on the set
                                Some(_) => {
                                    println!("equiv: {:?}", equivocation);
                                    acc_prime.remove(&equivocation)
                                }
                                // add the vote
                                None => {
                                    // println!("no_equiv: {:?}", equivocation);
                                    acc_prime.insert((*m).clone())
                                }
                            };
                        }
                        acc_prime // returns it
                    }
                    _ => recursor(m.justification(), acc_prime),
                }
            })
        }

        let j = latest_msgs
            .iter()
            .fold(Justification::empty(), |mut acc, m| {
                acc.insert(m.clone());
                acc
            });
        // start recursion
        recursor(&j, HashSet::new())
    }
}

type Voter = u32;
pub type VoteMsg = message::Message<VoteCount, Voter>;

//impl Sender for Voter {}

#[derive(Debug)]
pub struct Error(&'static str);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "{}", self.0)
    }
}

impl std::error::Error for Error {}

impl std::convert::From<&'static str> for Error {
    fn from(e: &'static str) -> Self {
        Error(e)
    }
}

impl Estimator for VoteCount {
    // the estimator just counts votes, which in this case are the unjustified
    // msgs
    type M = VoteMsg;
    type Error = Error;

    // Data could be anything, as it will not be used, will just pass None to
    // mk_estimate, as it takes an Option
    // type Data = Self;

    fn estimate<U: WeightUnit>(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        _weights: &sender::Weights<Voter, U>, // all voters have same weight
    ) -> Result<Self, Self::Error> {
        // the estimates are actually the original votes of each of the voters /
        // validators

        let votes = Self::get_vote_msgs(latest_msgs);
        let votes = votes
            .iter()
            .fold(Self::ZERO, |acc, vote| acc + vote.estimate().clone());
        Ok(votes)
    }
}
