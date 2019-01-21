use std::collections::HashSet;
use std::fmt::{Debug, Formatter};
use std::ops::Add;

#[cfg(feature = "integration_test")]
use proptest::prelude::*;

use justification::{Justification, LatestMsgsHonest};
use message::{CasperMsg, Message};
use senders_weight::SendersWeight;
use traits::{Estimate, Sender, Zero};
#[derive(Clone, Eq, Ord, PartialOrd, PartialEq, Hash, Default, serde_derive::Serialize)]
pub struct VoteCount {
    yes: u32,
    no: u32,
}

#[cfg(feature = "integration_test")]
impl<S: Sender> From<S> for VoteCount {
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
    #[cfg(feature = "integration_test")]
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
    pub fn create_vote_msg(sender: u32, vote: bool) -> Message<Self, u32> {
        let justification = Justification::new();
        let estimate = match vote {
            true => VoteCount { yes: 1, no: 0 },
            false => VoteCount { yes: 0, no: 1 },
        };

        Message::new(sender, justification, estimate, None)
    }

    ///
    fn get_vote_msgs(
        latest_msgs: &LatestMsgsHonest<Message<Self, Voter>>,
    ) -> HashSet<Message<Self, Voter>> {
        fn recursor(
            latest_msgs: &Justification<Message<VoteCount, Voter>>,
            acc: HashSet<Message<VoteCount, Voter>>,
        ) -> HashSet<Message<VoteCount, Voter>> {
            latest_msgs.iter().fold(acc, |mut acc_prime, m| {
                match m.justification().len() {
                    0 => {
                        // vote found, vote is a message with 0 justification
                        let estimate = m.estimate().clone();
                        if VoteCount::is_valid_vote(&estimate) {
                            let equivocation = Message::new(
                                m.sender().clone(),
                                m.justification().clone(),
                                VoteCount::toggle_vote(&estimate),
                                None,
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

        let j = latest_msgs.iter().fold(Justification::new(), |mut acc, m| {
            acc.insert(m.clone());
            acc
        });
        // start recursion
        recursor(&j, HashSet::new())
    }
}

type Voter = u32;
pub type VoteMsg = Message<VoteCount, Voter>;

impl Sender for Voter {}

impl Estimate for VoteCount {
    // the estimator just counts votes, which in this case are the unjustified
    // msgs
    type M = VoteMsg;

    // Data could be anything, as it will not be used, will just pass None to
    // mk_estimate, as it takes an Option
    // type Data = Self;

    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        _weights: &SendersWeight<Voter>, // all voters have same weight
    ) -> Result<Self, &'static str> {
        // the estimates are actually the original votes of each of the voters /
        // validators

        let votes = Self::get_vote_msgs(latest_msgs);
        let votes = votes
            .iter()
            .fold(Self::ZERO, |acc, vote| acc + vote.estimate().clone());
        Ok(votes)
    }
}

#[cfg(tests)]
mod count_votes {

    use std::collections::HashSet;

    use super::*;
    use justification::{Justification, LatestMsgs};
    use message::{CasperMsg, Message};

    #[test]
    fn count_votes() {
        use justification::SenderState;
        use senders_weight::SendersWeight;

        let senders_weights =
            SendersWeight::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());

        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = &VoteCount::create_vote_msg(1, true);
        let mut j0 = Justification::new();

        let weights = SenderState::new(
            senders_weights,
            0.0,
            None,
            LatestMsgs::new(),
            2.0,
            HashSet::new(),
        );

        let (success, _) = j0.faulty_inserts(vec![v0].iter().cloned().collect(), &weights);
        assert!(success);

        let (m0, _) = &Message::from_msgs(0, vec![v0], None, &weights, None).unwrap();
        let mut j1 = Justification::new();
        let (success, _) = j1.faulty_inserts(vec![v1].iter().cloned().collect(), &weights);
        assert!(success);

        let (success, _) = j1.faulty_inserts(vec![m0].iter().cloned().collect(), &weights);
        assert!(success);

        let (m1, _) = &Message::from_msgs(1, vec![v1, m0], None, &weights, None).unwrap();
        assert_eq!(
            Message::estimate(m1).clone(),
            VoteCount { yes: 1, no: 1 },
            "should have 1 yes, and 1 no vote, found {:?}",
            Message::estimate(m1).clone(),
        );

        let (success, _) = j1.faulty_inserts(vec![v0_prime].iter().cloned().collect(), &weights);
        assert!(success);

        let (m1_prime, _) = &Message::from_msgs(
            1,
            vec![v1, m0, v0_prime].iter().cloned().collect(),
            None,
            &weights,
            None,
        )
        .unwrap();
        assert_eq!(
            Message::estimate(m1_prime).clone(),
            VoteCount { yes: 1, no: 0 },
            "should have 1 yes, and 0 no vote, found {:?}, the equivocation vote should cancels out the normal vote",
            Message::estimate(&m1_prime).clone())
    }
}
