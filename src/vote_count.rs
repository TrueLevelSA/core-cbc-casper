use std::collections::{HashSet};
use std::ops::{Add};
use std::fmt::{Debug, Formatter, Result};
use std::sync::{Arc};

use traits::{Zero, Estimate, Sender};
use message::{Message, AbstractMsg};
use justification::{Justification};

#[derive(Clone, Eq, Ord, PartialOrd, PartialEq, Hash, Default)]
pub struct VoteCount {
    yes: u32,
    no: u32,
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
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "y{:?}/n{:?}", self.yes, self.no)
    }
}

impl Sender for u32 {}

impl VoteCount {
    // makes sure nobody adds more than one vote to their unjustified VoteCount
    // object. if they did, their vote is invalid and will be ignored
    fn is_valid_vote(vote: &Option<Self>) -> bool {
        // these two are the only allowed votes (unjustified msgs)
        match vote {
            Some(VoteCount { yes: 1, no: 0 }) => true,
            Some(VoteCount { yes: 0, no: 1 }) => true,
            _ => false,
        }
    }

    // used to create an equivocation vote
    fn toggle_vote(vote: &Option<Self>) -> Option<Self> {
        // these two are the only allowed votes (unjustified msgs)
        match vote {
            Some(VoteCount { yes: 1, no: 0 }) =>
                Some(VoteCount { yes: 0, no: 1 }),
            Some(VoteCount { yes: 0, no: 1 }) =>
                Some(VoteCount { yes: 1, no: 0 }),
            _ => None,
        }
    }

    pub fn create_vote_msg(sender: u32, vote: bool) -> Arc<Message<Self, u32>> {
        let justification = Justification::new();
        let estimate = match vote {
            true => Some(VoteCount { yes: 1, no: 0 }),
            false => Some(VoteCount { yes: 0, no: 1 }),
        };

        Message::new(sender, justification, estimate)
    }

    fn get_vote_msgs(
        msg: &Arc<Message<Self, Voter>>,
    ) -> HashSet<Arc<Message<Self, Voter>>> {
        fn recursor(
            msg: &Arc<Message<VoteCount, Voter>>,
            acc: HashSet<Arc<Message<VoteCount, Voter>>>,
        ) -> HashSet<Arc<Message<VoteCount, Voter>>> {
            let justification = Message::get_justification(msg);
            justification.iter().fold(acc, |mut acc_prime, m| {
                match justification.len() {
                    0 => {
                        // vote found, vote is a message with 0 justification
                        let estimate = Message::get_estimate(m);
                        if VoteCount::is_valid_vote(estimate) {
                            let equivocation = Message::new(
                                Message::get_sender(m).clone(),
                                Message::get_justification(m).clone(),
                                VoteCount::toggle_vote(estimate),
                            );
                            // search for the equivocation of the current msg
                            match acc_prime.get(&equivocation) {
                                // remove the equivoted vote, none of the pair
                                // will stay on the set
                                Some(_) => acc_prime.remove(&equivocation),
                                // add the vote
                                None => acc_prime.insert((*m).clone()),
                            };
                        }
                        acc_prime // returns it
                    },
                    _ => recursor(&m, acc_prime),
                }
            })
        }
        // start recursion
        recursor(msg, HashSet::new())
    }
}

type Voter = u32;

impl Estimate for VoteCount {
    // the estimator just counts votes, which in this case are the unjustified
    // msgs
    type M = Message<Self, Voter>;
    fn estimator(justification: &Justification<Self::M>) -> Self {
        // stub msg w/ no estimate and no sender that will be dropped on the
        // pattern matching below
        let msg = Message::new(
            ::std::u32::MAX, // sender,
            justification.clone(),
            None, // estimate, will be droped on the pattern matching below
        );
        // the estimates are actually the original votes of each of the voters /
        // validators
        let votes = Self::get_vote_msgs(&msg);
        votes.iter().fold(Self::ZERO, |acc, vote| {
            match Message::get_estimate(vote) {
                Some(estimate) => acc + estimate.clone(),
                None => acc, // skip counting
            }
        })
    }
}

mod count_votes {
    use super::*;
    fn new_msg(
        sender: u32,
        justifications: Justification<Message<VoteCount, u32>>,
    ) -> Arc<Message<VoteCount, u32>> {
        let estimate = VoteCount::estimator(&justifications);
        Message::new(sender, justifications, Some(estimate))
    }

    #[test]
    fn count_votes() {
        use justification::{Weights};
        use sender_weight::{SendersWeight};
        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        );
        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = &VoteCount::create_vote_msg(1, true);
        let mut j0 = Justification::new();
        let weights = Weights::new(senders_weights, 0.0, 2.0);
        assert!(j0.faulty_insert(v0, weights.clone()).success);
        let m0 = &new_msg(0, j0);
        let mut j1 = Justification::new();
        assert!(j1.faulty_insert(v1, weights.clone()).success);
        assert!(j1.faulty_insert(m0, weights.clone()).success);

        let m1 = &new_msg(1, j1.clone());
        assert_eq!(
            Message::get_estimate(m1).clone().unwrap(),
            VoteCount { yes: 1, no: 1 },
            "should have 1 yes, and 1 no vote, found {:?}",
            Message::get_estimate(m1).clone().unwrap(),
        );

        assert!(j1.faulty_insert(v0_prime, weights.clone()).success);
        let m1_prime = &new_msg(1, j1.clone());
        assert_eq!(
            Message::get_estimate(m1_prime).clone().unwrap(),
            VoteCount { yes: 1, no: 0 },
            "should have 1 yes, and 0 no vote, found {:?}, the equivocation vote should cancels out the normal vote",
            Message::get_estimate(&m1_prime).clone().unwrap(),
        )
    }
}
