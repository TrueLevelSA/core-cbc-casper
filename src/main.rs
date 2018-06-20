#![allow(dead_code)]

use std::f64;
use std::collections::{BTreeSet, HashSet, HashMap};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Add};

type Sender = u32;

// the options in message below r now used to initiate some recursions w/ stub
// msgs
#[derive(Eq, Ord, PartialOrd)]
struct Message<'m, E: 'm + Hash + Ord> {
    estimate: Option<E>,
    sender: Option<Sender>,
    justifications: Justifications<'m, E>,
}

impl<'m, E> Message<'m, E>
where
    E: Estimate + Clone,
{
    fn new(
        sender: Sender,
        justifications: Justifications<'m, E>,
    ) -> Message<'m, E> {
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
    // does m1 equivocates with m2?
    fn equivocates(m1: &Self, m2: &Self) -> bool {
        // the estimate bit below is necessary due to the definition of equality
        // of messages (the estimate is not a function of the equality). see
        // tests for equality of messages.
        let equal_msgs = m1 == m2 && m1.estimate == m2.estimate;
        !equal_msgs
            && m1.sender == m2.sender
            && !Self::depends(m1, m2)
            && !Self::depends(m2, m1)
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
        // self.estimate.hash(state); // the hash of the msg does NOT depend on the estimate
    }
}

impl<'m, E: Hash + Ord> PartialEq for Message<'m, E> {
    fn eq(&self, other: &Message<'m, E>) -> bool {
        self.sender == other.sender
            && self.justifications == other.justifications
        // && self.estimate == other.estimate
    }
}

impl<'m, E: Hash + Ord> fmt::Debug for Message<'m, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Message {{ sender: {}}} -> {:?}",
            self.sender.unwrap_or(Sender::max_value()),
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

struct FaultyInsertResult<'w> {
    success: bool,
    weights: Weights<'w>,
}

type WeightUnit = f64;

#[derive(Debug)]
struct Weights<'w> {
    fault_weight: WeightUnit,
    sender_weights: &'w HashMap<Sender, WeightUnit>,
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
    fn get_msg_fault_weight(
        &self,
        msg: &'m Message<'m, E>,
        sender_weights: &HashMap<Sender, WeightUnit>,
    ) -> WeightUnit {
        self.latest_msgs.iter().fold(0.0, |acc, m| {
            if Message::equivocates(m, msg) {
                acc + sender_weights[&m.sender.unwrap_or(Sender::max_value())]
            }
            else {
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
        let msg_fault_weight =
            self.get_msg_fault_weight(msg, &weights.sender_weights);
        let new_fault_weight = weights.fault_weight + msg_fault_weight;
        // no conflicts, msg added to the set
        if msg_fault_weight < f64::EPSILON {
            FaultyInsertResult {
                success: self.latest_msgs.insert(msg),
                weights,
            }
        }
        else if new_fault_weight <= weights.thr {
            let success = self.latest_msgs.insert(msg);
            let weights = if success {
                Weights {
                    fault_weight: new_fault_weight,
                    ..weights
                }
            }
            else {
                weights
            };

            FaultyInsertResult { success, weights }
        }
        // conflicting message NOT added to the set as it crosses the fault
        // weight thr
        else {
            FaultyInsertResult {
                success: false,
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
    fn is_valid(i: &Option<Self>) -> bool;
}

impl Estimate for VoteCount {
    // makes sure nobody adds more than one vote to their unjustified VoteCount
    // object. if they did, their vote is invalid and will be ignored
    fn is_valid(vote: &Option<Self>) -> bool {
        // these two are the only allowed votes (unjustified msgs)
        vote == &Some(VoteCount { yes: 1, no: 0 })
            || vote == &Some(VoteCount { yes: 0, no: 1 })
    }
    // the estimator just counts votes, which in this case are the unjustified
    // msgs
    fn estimator(justifications: Justifications<Self>) -> Self {
        // stub msg w/ no estimate and no sender
        let msg = Message {
            estimate: None,
            sender: None,
            justifications,
        };
        let votes = Self::get_vote_msgs(&msg, HashSet::new());
        votes
            .iter()
            .filter(|v| {
                // the estimate here is actually the original votes of each of
                // the voters / validators
                Self::is_valid(&v.estimate)
            })
            .fold(Self::ZERO, |acc, vote| {
                match &vote.estimate {
                    Some(estimate) => acc + estimate.clone(),
                    None => acc, // skip counting
                }
            })
    }
}

// the value $z$ that, when added to other value $x$ of same type, returns the
// other value x: $x + z = x$
trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialOrd, Hash)]
struct VoteCount {
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
            .fold(acc, |mut acc_new, m| {
                match m.justifications.latest_msgs.len() {
                    0 => {
                        // vote found, vote is a message with 0 justifications
                        acc_new.insert(m); // mutates acc_new
                        acc_new // returns it
                    },
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
fn main() {
    let v0 = VoteCount::create_vote_msg(0, false);
    let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote

    // v0 and v0_prime are equivocating messages (first child of a fork). To
    // enforce that both of them cannot be included in the same set (in a
    // hashset) both v0 and v0_prime should hash to the same value, and should
    // be considered equal, and only one of them could live in the set. To
    // achieve that, the vote itself doesn't count, just sender and
    // justification contributes to the hash (here justification is empty).
    // TODO: What about when a fork happens and the justifications are different
    // but at the same height, i should handle that.

    assert!(v0 == v0_prime, "v0 and v0_prime should be equal");

    let v1 = VoteCount::create_vote_msg(1, true);
    assert!(v0 != v1);
    // let v1_prime = VoteCount::create_vote_msg(1, false);

    // let v2 = VoteCount::create_vote_msg(2, true, 0);
    // let v3 = VoteCount::create_vote_msg(3, true, 0);

    let sender_weights =
        [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect();

    let mut j0 = Justifications::new();
    assert!(
        j0.faulty_insert(
            &v0,
            Weights {
                sender_weights: &sender_weights,
                fault_weight: 0.0,
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

    let mut j1 = Justifications::new();
    assert!(
        j1.faulty_insert(
            &v1,
            Weights {
                sender_weights: &sender_weights,
                fault_weight: 0.0,
                thr: 0.0,
            }
        ).success
    );
    assert!(
        j1.faulty_insert(
            &m0,
            Weights {
                sender_weights: &sender_weights,
                fault_weight: 0.0,
                thr: 0.0,
            }
        ).success
    );

    assert!(
        !j1.faulty_insert(
            &v0_prime,
            Weights {
                sender_weights: &sender_weights,
                fault_weight: 0.0,
                thr: 0.0
            }
        ).success,
        "$v0_prime$ should conflict with $v0$ through $m0$"
    );

    assert!(
        j1.clone()
            .faulty_insert(
                &v0_prime,
                Weights {
                    sender_weights: &sender_weights,
                    fault_weight: 0.0,
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
                    sender_weights: &sender_weights,
                    fault_weight: 0.0,
                    thr: 1.0
                }
            )
            .weights.fault_weight,
        1.0,
        "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set, and thus the fault_weight should be incremented to 1.0"
    );

    assert!(
        !j1.clone()
            .faulty_insert(
                &v0_prime,
                Weights {
                    sender_weights: &sender_weights,
                    fault_weight: 0.1,
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
                    sender_weights: &sender_weights,
                    fault_weight: 0.1,
                    thr: 1.0
                }
            )
            .weights.fault_weight,
        0.1,
        "$v0_prime$ conflicts with $v0$ through $m0$, and we should not accept this fault as the fault threshold gets crossed for the set, and thus the fault_weight should not be incremented"
    );

    assert!(
        j1.clone()
            .faulty_insert(
                &v0_prime,
                Weights {
                    sender_weights: &sender_weights,
                    fault_weight: 1.0,
                    thr: 2.0
                }
            )
            .success,
        "$v0_prime$ conflict with $v0$ through $m0$, but we should accept this fault as the thr doesnt get crossed for the set"
    );

    let m1 = Message::new(1, j1);
    assert_eq!(
        m1.estimate,
        Some(VoteCount { yes: 1, no: 1 }),
        "should have 1 yes, and 1 no vote, found {:?}",
        m1.estimate
    );
    assert!(Message::depends(&m1, &v0), "m1 depends on v0 through m0");
    assert!(Message::depends(&m0, &v0), "m0 depends on v0 directly");

    // println!();
    // let mut j2 = Justifications::new();
    // let FaultyInsertResult {
    //     weights: Weights { fault_weight, .. },
    //     ..
    // } = j2.faulty_insert(
    //     &m0,
    //     Weights {
    //         sender_weights: &sender_weights,
    //         fault_weight: 0.0,
    //         thr: 3.0,
    //     },
    // );
    // println!("{:?}a", fault_weight);

    // let FaultyInsertResult {
    //     weights: Weights { fault_weight, .. },
    //     ..
    // } = j2.faulty_insert(
    //     &v1_prime,
    //     Weights {
    //         sender_weights: &sender_weights,
    //         fault_weight,
    //         thr: 3.0,
    //     },
    // );
    // println!("{:?}b", fault_weight);

    // let FaultyInsertResult {
    //     weights: Weights { fault_weight, .. },
    //     ..
    // } = j2.faulty_insert(
    //     &v0_prime,
    //     Weights {
    //         sender_weights: &sender_weights,
    //         fault_weight,
    //         thr: 3.0,
    //     },
    // );
    // println!("{:?}c", fault_weight);

    // assert!(Message::depends(&m0, &m0), "m0 depends on m0 directly");

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
}
