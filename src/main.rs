#![allow(dead_code)]

use std::collections::{BTreeSet, HashMap, HashSet};
use std::f64;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Add;

type Sender = u32;

// the options in message below r now used to initiate some recursions (the last
// leave of a tree) w/ stub msgs
#[derive(Eq, Ord, PartialOrd, Clone)]
struct Message<'m, E: 'm + Hash + Ord> {
    estimate: Option<E>,
    sender: Option<Sender>,
    justifications: Justifications<'m, E>,
}

impl<'m, E> Message<'m, E>
where
    E: Estimate + Clone,
{
    fn new(sender: Sender, justifications: Justifications<'m, E>) -> Message<'m, E> {
        Message {
            estimate: Some(E::estimator(justifications.clone())),
            sender: Some(sender),
            justifications,
        }
    }
    // does m1 depend on m2?
    fn depends(m1: &Self, m2: &Self) -> bool {
        m1.justifications.latest_msgs.iter().fold(
            m1.justifications.latest_msgs.contains(m2),
            // although this recursion ends supposedly only at genesis message,
            // the trick is the following: it short-circuits while descending on
            // the dependency tree, if it finds a dependent message. when
            // dealing with honest validators, this would return true very fast.
            // all the new derived branches of the justification can be
            // evaluated in parallel, when using par_iter() instead of iter().
            |acc, m1_prime| acc || Self::depends(m1_prime, m2),
        )
    }
    // does m1 equivocate with m2?
    fn equivocates(m1: &Self, m2: &Self) -> bool {
        m1 != m2 && m1.sender == m2.sender && !Self::depends(m1, m2) && !Self::depends(m2, m1)
    }
}

// what happens if in the justification of one of the messages theres a message
// that is newer than the one referred to in the current justification?

// what happens if a sender does not reference his latest message, but
// references a msg that references his last message (this wouldnt be an
// equivocation)

impl<'m, E: Hash + Ord> Hash for Message<'m, E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.sender.hash(state);
        self.justifications.hash(state);
        self.estimate.hash(state); // the hash of the msg does NOT depend on the estimate
    }
}

impl<'m, E: Hash + Ord> PartialEq for Message<'m, E> {
    fn eq(&self, other: &Message<'m, E>) -> bool {
        self.sender == other.sender
            && self.justifications == other.justifications
            && self.estimate == other.estimate
    }
}

impl<'m, E: Hash + Ord> fmt::Debug for Message<'m, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Message {{ sender: {}}} -> {:?}",
            self.sender.unwrap_or(Sender::max_value()), // TODO: handle this
            self.justifications
        )
    }
}

// make sure only latest messages can get in the set
#[derive(Eq, PartialEq, Hash, PartialOrd, Ord, Clone)]
struct Justifications<'m, E: 'm + Hash + Ord> {
    latest_msgs: BTreeSet<&'m Message<'m, E>>,
}
// prev_msg: Option<&'m Message<'m>>,

// TODO: BTreeSet is ordered, but all nodes should be able to compute the same
// ordered set based on the content of the message and not memory addresses

// impl Hash for Justifications { }

type WeightUnit = f64;

impl Zero<WeightUnit> for WeightUnit {
    const ZERO: Self = 0.0f64;
    fn is_zero(val: &Self) -> bool {
        val < &f64::EPSILON && val > &-f64::EPSILON
    }
}

struct FaultyInsertResult<'w> {
    success: bool,
    msg_fault_weight: WeightUnit,
    weights: Weights<'w>,
}

struct FaultyInsert<'w> {
    msg_fault_weight: WeightUnit,
    weights: Weights<'w>,
}

#[derive(Debug, Clone)]
struct Weights<'w> {
    state_fault_weight: WeightUnit,
    senders_weights: &'w HashMap<Sender, WeightUnit>,
    thr: WeightUnit,
}

impl<'m, E> Justifications<'m, E>
where
    E: Estimate + Clone,
{
    fn new() -> Self {
        Justifications {
            latest_msgs: BTreeSet::new(),
        }
    }

    // fn equivocates(&self, msg: &'m Message<'m, E>) -> bool {
    //     self.latest_msgs
    //         .iter()
    //         .fold(false, |acc, m| acc || Message::equivocates(m, msg))
    // }

    // get the additional fault weight to be added to the state when inserting
    // msg to the state / justification
    fn get_msg_fault_weight_overhead(
        &self,
        msg: &'m Message<'m, E>,
        senders_weights: &HashMap<Sender, WeightUnit>,
    ) -> Option<WeightUnit> {
        self.latest_msgs
            .iter()
            .fold(Some(WeightUnit::ZERO), |acc, m| {
                if Message::equivocates(m, msg) {
                    m.sender
                        .and_then(|sender| senders_weights.get(&sender))
                        .and_then(|weight| acc.and_then(|acc| Some(acc + weight)))
                } else {
                    acc
                }
            })
    }
    // insert msgs to the Justification, accepting up to $thr$ faults by sender's
    // weight
    fn faulty_insert(
        &mut self,
        msg: &'m Message<'m, E>,
        // FIXME: not sure about the following lifetime, i believe it can be shorter
        weights: Weights<'m>,
    ) -> FaultyInsertResult {
        // if it fails to unwrap, nan ends up in the else branch
        let msg_fault_weight = self
            .get_msg_fault_weight_overhead(msg, &weights.senders_weights)
            .unwrap_or(f64::NAN);

        if msg_fault_weight.is_nan() {
            println!("msg overhead failed")
        }

        let new_fault_weight = weights.state_fault_weight + msg_fault_weight;

        // no conflicts, msg added to the set
        if WeightUnit::is_zero(&msg_fault_weight) {
            FaultyInsertResult {
                success: self.latest_msgs.insert(msg),
                msg_fault_weight,
                weights,
            }
        } else if new_fault_weight <= weights.thr {
            let success = self.latest_msgs.insert(msg);
            let weights = if success {
                Weights {
                    state_fault_weight: new_fault_weight,
                    ..weights
                }
            } else {
                weights
            };

            FaultyInsertResult {
                success,
                msg_fault_weight,
                weights,
            }
        }
        // conflicting message NOT added to the set as it crosses the fault
        // weight thr OR get_msg_fault_weight_overhead returned None
        else {
            FaultyInsertResult {
                success: false,
                msg_fault_weight,
                weights,
            }
        }
    }
}

impl<'m, E: Hash + Ord> fmt::Debug for Justifications<'m, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.latest_msgs)
    }
}

trait Estimate: Hash + Ord + Sized {
    fn estimator(justifications: Justifications<Self>) -> Self;
    // fn is_valid(i: &Option<Self>) -> bool;
}

impl Estimate for VoteCount {
    // the estimator just counts votes, which in this case are the unjustified
    // msgs
    fn estimator(justifications: Justifications<Self>) -> Self {
        // stub msg w/ no estimate and no sender
        let msg = Message {
            estimate: None,
            sender: None,
            justifications,
        };
        // the estimates are actually the original votes of each of the voters /
        // validators
        let votes = Self::get_vote_msgs(&msg, HashSet::new());
        votes.iter().fold(Self::ZERO, |acc, vote| {
            match &vote.estimate {
                Some(estimate) => acc + estimate.clone(),
                None => acc, // skip counting
            }
        })
    }
}

// the value $z$ that, when added to other value $x$ of same type, returns the
// other value x: $z + x = x$
trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialOrd, Hash)]
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

impl PartialEq for VoteCount {
    fn eq(&self, other: &VoteCount) -> bool {
        self.yes == other.yes && self.no == other.no
    }
}

impl VoteCount {
    // makes sure nobody adds more than one vote to their unjustified VoteCount
    // object. if they did, their vote is invalid and will be ignored
    fn is_valid_vote(vote: &Option<Self>) -> bool {
        // these two are the only allowed votes (unjustified msgs)
        vote == &Some(VoteCount { yes: 1, no: 0 }) || vote == &Some(VoteCount { yes: 0, no: 1 })
    }

    // used to create an equivocation vote
    fn toggle_vote(vote: &Option<Self>) -> Option<Self> {
        // these two are the only allowed votes (unjustified msgs)
        match vote {
            Some(VoteCount { yes: 1, no: 0 }) => Some(VoteCount { yes: 0, no: 1 }),
            Some(VoteCount { yes: 0, no: 1 }) => Some(VoteCount { yes: 1, no: 0 }),
            Some(VoteCount { yes: _, no: _ }) => None,
            None => None,
        }
    }

    fn create_vote_msg<'m>(sender: Sender, vote: bool) -> Message<'m, Self> {
        let justifications: Justifications<Self> = Justifications::new();
        Message {
            estimate: match vote {
                true => Some(VoteCount { yes: 1, no: 0 }),
                false => Some(VoteCount { yes: 0, no: 1 }),
            },
            sender: Some(sender),
            justifications,
        }
    }

    fn get_vote_msgs<'m>(
        msg: &'m Message<Self>,
        acc: HashSet<&'m Message<Self>>,
    ) -> HashSet<&'m Message<'m, Self>> {
        msg.justifications
            .latest_msgs
            .iter()
            .fold(acc, |mut acc_new, &m| {
                match m.justifications.latest_msgs.len() {
                    0 => {
                        // vote found, vote is a message with 0 justifications
                        // TODO: prevent double vote
                        if Self::is_valid_vote(&m.estimate) {
                            let equivocation = Message {
                                estimate: Self::toggle_vote(&m.estimate),
                                ..m.clone()
                            };
                            // search for the equivocation of the current msg
                            match acc_new.get(&equivocation) {
                                // remove the equivoted vote, none of the pair
                                // will stay on the set
                                Some(_) => acc_new.remove(&equivocation),
                                // add the vote
                                None => acc_new.insert(m),
                            };
                        }
                        acc_new // returns it
                    }
                    _ => Self::get_vote_msgs(m, acc_new),
                }
            })
    }
}
// // show that each vote was seen by all validators
// fn votes_seen<'m>(msg: &'m Message<'m>, mut senders: &'m Vec<Sender>, acc: HashSet<(&'m Message<'m>, &'m Vec<Sender>)>) -> HashSet<(&'m Message<'m>, &'m Vec<Sender>)> {
//     msg.justifications.iter()
//         .fold(acc, |mut acc_new, m| {
//             match m.justifications.len() {
//                 0 => { // vote found, vote is a message with 0 justifications
//                     acc_new.insert((m, &senders)); // mutates acc_new
//                     acc_new // returns the mutated acc_new
//                 },
//                 _ => {
//                     senders.push(m.sender);
//                     votes_seen(m, &senders.clone(), acc_new)
//                 },
//             }
//         })
// }

fn main() {}

#[cfg(test)]
mod main {
    use {Justifications, Message, VoteCount, Weights};

    #[test]
    fn msg_equality() {
        // v0 and v0_prime are equivocating messages (first child of a fork).
        let v0 = VoteCount::create_vote_msg(0, false);
        let v1 = VoteCount::create_vote_msg(1, true);
        let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote
        let v0_idem = VoteCount::create_vote_msg(0, false);
        assert!(v0 == v0_idem, "v0 and v0_idem should be equal");
        assert!(v0 != v0_prime, "v0 and v0_prime should NOT be equal");
        assert!(v0 != v1, "v0 and v1 should NOT be equal");

        let senders_weights = [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect();
        let mut j0 = Justifications::new();
        assert!(
            j0.faulty_insert(
                &v0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m0 = Message::new(0, j0.clone());

        let mut j1 = Justifications::new();
        assert!(
            j1.faulty_insert(
                &v0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );

        assert!(
            j1.faulty_insert(
                &m0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        assert!(
            Message::new(0, j0.clone()) == Message::new(0, j0.clone()),
            "messages should be equal"
        );
        assert!(Message::new(0, j0.clone()) != Message::new(0, j1.clone()));
    }

    #[test]
    fn msg_depends() {
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote

        let senders_weights = [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect();

        let mut j0 = Justifications::new();
        assert!(
            j0.faulty_insert(
                &v0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m0 = Message::new(0, j0);
        assert!(
            !Message::depends(&v0, &v0_prime),
            "v0 does NOT depends on v0_prime as they are equivocating"
        );
        assert!(
            !Message::depends(&m0, &m0),
            "m0 does NOT depends on itself directly, by our impl choice"
        );
        assert!(
            !Message::depends(&m0, &v0_prime),
            "m0 depends on v0 directly"
        );
        assert!(Message::depends(&m0, &v0), "m0 depends on v0 directly");

        let mut j0 = Justifications::new();
        assert!(
            j0.faulty_insert(
                &v0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m0 = Message::new(0, j0.clone());

        let mut j1 = Justifications::new();
        assert!(
            j1.faulty_insert(
                &v0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );

        assert!(
            j1.faulty_insert(
                &m0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m1 = &Message::new(0, j1.clone());
        assert!(Message::depends(&m1, &m0), "m1 DOES depent on m0");
        assert!(!Message::depends(&m0, &m1), "but m0 does NOT depend on m1");
        assert!(Message::depends(&m1, &v0), "m1 depends on v0 through m0");
    }

    #[test]
    fn msg_equivocates() {
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = VoteCount::create_vote_msg(1, true);

        let senders_weights = [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect();

        let mut j0 = Justifications::new();
        assert!(
            j0.faulty_insert(
                &v0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m0 = Message::new(0, j0);
        assert_eq!(
            m0.estimate,
            Some(VoteCount { yes: 0, no: 1 }),
            "should have 0 yes, and 1 no vote, found {:?}",
            m0.estimate
        );
        assert!(!Message::equivocates(&v0, &v0), "should be all good");
        assert!(!Message::equivocates(&v1, &m0), "should be all good");
        assert!(!Message::equivocates(&m0, &v1), "should be all good");
        assert!(
            Message::equivocates(&v0, &v0_prime),
            "should be a direct equivocation"
        );
        assert!(
            Message::equivocates(&m0, &v0_prime),
            "should be an indirect equivocation, equivocates to m0 through v0"
        );
    }

    #[test]
    fn faulty_inserts() {
        let senders_weights = [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect();
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = VoteCount::create_vote_msg(1, true);
        let mut j0 = Justifications::new();
        assert!(
            j0.faulty_insert(
                &v0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m0 = Message::new(0, j0);
        let mut j1 = Justifications::new();
        assert!(
            j1.faulty_insert(
                &v1,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        assert!(
            j1.faulty_insert(
                &m0,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        assert!(
            !j1.faulty_insert(
                &v0_prime,
                Weights {
                    senders_weights: &senders_weights,
                    state_fault_weight: 0.0,
                    thr: 0.0
                }
            ).success,
            "$v0_prime$ should conflict with $v0$ through $m0$, and we should reject as our fault tolerance thr is zero"
        );
        assert!(
            j1.clone()
                .faulty_insert(
                    &v0_prime,
                    Weights {
                        senders_weights: &senders_weights,
                        state_fault_weight: 0.0,
                        thr: 1.0
                    }
                )
                .success,
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set"
        );

        assert_eq!(
            j1.clone()
                .faulty_insert(
                    &v0_prime,
                    Weights {
                        senders_weights: &senders_weights,
                        state_fault_weight: 0.0,
                        thr: 1.0
                    }
                )
                .weights.state_fault_weight,
            1.0,
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set, and thus the state_fault_weight should be incremented to 1.0"
        );

        assert!(
            !j1.clone()
                .faulty_insert(
                    &v0_prime,
                    Weights {
                        senders_weights: &senders_weights,
                        state_fault_weight: 0.1,
                        thr: 1.0
                    }
                )
                .success,
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should not accept this fault as the fault threshold gets crossed for the set"
        );

        assert_eq!(
            j1.clone()
                .faulty_insert(
                    &v0_prime,
                    Weights {
                        senders_weights: &senders_weights,
                        state_fault_weight: 0.1,
                        thr: 1.0
                    }
                )
                .weights.state_fault_weight,
            0.1,
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should NOT accept this fault as the fault threshold gets crossed for the set, and thus the state_fault_weight should not be incremented"
        );

        assert!(
            j1.clone()
                .faulty_insert(
                    &v0_prime,
                    Weights {
                        senders_weights: &senders_weights,
                        state_fault_weight: 1.0,
                        thr: 2.0
                    }
                )
                .success,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should accept this fault as the thr doesnt get crossed for the set"
        );

        assert!(
            !j1.clone()
                .faulty_insert(
                    &v0_prime,
                    Weights {
                        senders_weights: &[].iter().cloned().collect(),
                        state_fault_weight: 1.0,
                        thr: 2.0
                    }
                )
                .success,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity"
        );

        assert_eq!(
            j1.clone()
                .faulty_insert(
                    &v0_prime,
                    Weights {
                        senders_weights: &[].iter().cloned().collect(),
                        state_fault_weight: 1.0,
                        thr: 2.0
                    }
                )
                .weights.state_fault_weight,
            1.0,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity, and thus the state_fault_weight should be unchanged"
        );
    }

    #[test]
    fn count_votes() {
        let senders_weights = [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect();
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = VoteCount::create_vote_msg(1, true);
        let mut j0 = Justifications::new();
        let weights = Weights {
            senders_weights: &senders_weights,
            state_fault_weight: 0.0,
            thr: 2.0,
        };
        assert!(j0.faulty_insert(&v0, weights.clone()).success);
        let m0 = Message::new(0, j0);
        let mut j1 = Justifications::new();
        assert!(j1.faulty_insert(&v1, weights.clone()).success);
        assert!(j1.faulty_insert(&m0, weights.clone()).success);

        let m1 = Message::new(1, j1.clone());
        assert_eq!(
            m1.estimate.clone().unwrap(),
            VoteCount { yes: 1, no: 1 },
            "should have 1 yes, and 1 no vote, found {:?}",
            m1.estimate
        );

        assert!(j1.faulty_insert(&v0_prime, weights.clone()).success,);
        let m1_prime = Message::new(1, j1.clone());
        assert_eq!(
            m1_prime.estimate.clone().unwrap(),
            VoteCount { yes: 1, no: 0 },
            "should have 1 yes, and 0 no vote, found {:?}, the equivocation vote should cancels out the normal vote",
            m1.estimate
        )
    }
}

// println!("m1: {:?}", m1);
// let mut j2 = Justifications::new(None); assert!(j2.insert(&v0)); assert!(j2.insert(&v0_prime));
// let m2 = Message::new(2, j2, 0);
// assert_eq!(Justifications::new([&v1, &m0, &v0].iter().cloned().collect(), Some(&m0)), Justifications::new([&v1, &m0, &v0_prime].iter().cloned().collect(), Some(&m0)));

// assert!(!m1.depends(&v0_prime), "m1 doesnt depends on v0_prime");

// println!("m0: {:?}", m0.justifications);
// println!("m1: {:?}", m1.justifications);

// let m2 = Message::new(0, Justifications{latest_msgs: [&m1].iter().cloned().collect()}, 1);
// let m3 = Message::new(0, Justifications{latest_msgs: [&v1].iter().cloned().collect()}, 2);
// println!("m2: {:?}", m2.justifications);
// println!("m3: {:?}", m3.justifications);

// println!("d: {:?}", m0.justifications.set.is_disjoint(&m1.justifications.set));

// let m1p = Message::new(1, [&v1, &v0_prime, &m0].iter().cloned().collect());
// assert!(m1p.estimate == Some(VoteCount {yes: 2, no: 0, sender: None}), "should have 2 yes, and 0 no vote, found {:?}", m1p.estimate);

// let m2 = Message::new(2, [&v2, &m0, &m1].iter().cloned().collect());
// assert!(m2.estimate == Some(VoteCount {yes: 2, no: 1, sender: None}), "should have 2 yes, and 1 no vote, found {:?}", m2.estimate);

// let m3 = Message::new(0, [&m0, &m1, &m2].iter().cloned().collect());
// assert!(m3.estimate == Some(VoteCount {yes: 2, no: 1, sender: None}), "should have 2 yes, and 1 no vote, found {:?}", m3.estimate);

// let m4 = Message::new(3, [&v3, &m0, &m1, &m2, &m3].iter().cloned().collect());
// assert!(m4.estimate == Some(VoteCount {yes: 3, no: 1, sender: None}), "should have 3 yes, and 1 no vote, found {:?}", m4.estimate);

// let m5 = Message::new(0, [&m0, &m1, &m2, &m3, &m4].iter().cloned().collect());
// assert!(m5.estimate == Some(VoteCount {yes: 3, no: 1, sender: None}), "should have 3 yes, and 1 no vote, found {:?}", m5.estimate);

// let m6 = Message::new(0, [&m5].iter().cloned().collect());
// assert!(m6.estimate == Some(VoteCount {yes: 3, no: 1, sender: None}), "should have 3 yes, and 1 no vote, found {:?}", m6.estimate);

// println!("m0: {:?}", m0.justifications.len());
// println!("m1: {:?}", m1.justifications.len());
// println!("m2: {:?}", m2.justifications.len());

// // let j5: HashSet<_> = [&m1, &m2, &m3].iter().cloned().collect();
// // let j6: HashSet<_> = [&m4].iter().cloned().collect();
// // // let m6 = Message::new(3, [&m0, &m1, &m2, &m3, &m4, &m5].iter().cloned().collect());
// // println!("{:?}", j5.len());
// // println!("{:?}", j6.len());
