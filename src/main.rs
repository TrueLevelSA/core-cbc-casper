// external
use std::collections::{BTreeSet, HashMap, HashSet};
use std::collections::btree_set::{Iter};
use std::{f64};
use std::hash::{Hash, Hasher};
use std::ops::{Add};
use std::fmt::{Display, Debug, Formatter, Result};
use std::sync::{Arc};
// the options in message below r now used to initiate some recursions (the base
// case) w/ stub msgs
#[derive(Eq, Ord, PartialOrd, Clone, Default)]
pub struct Message<E, S>
where
    E: Estimate,
    S: Sender,
{
    estimate: Option<E>,
    sender: Option<S>,
    justifications: Justification<Message<E, S>>,
}

impl<E, S> Message<E, S>
where
    E: Estimate<M = Self>,
    S: Sender,
{
    fn new(sender: S, justifications: Justification<Self>) -> Arc<Self> {
        Arc::new(Self {
            estimate: Some(E::estimator(&justifications)),
            sender: Some(sender),
            justifications,
        })
    }
}

pub trait AbstractMsg: Hash + Ord + Clone + Debug + Default + Eq {
    type E: Estimate;
    type S: Sender;
    fn get_sender(Arc<Self>) -> Option<Self::S>;
    fn get_estimate(Arc<Self>) -> Option<Self::E>;
    fn get_justifications(Arc<Self>) -> Justification<Self>;
    fn equivocates(m1: Arc<Self>, m2: Arc<Self>) -> bool {
        m1.clone() != m2.clone()
            && Self::get_sender(m1.clone()) == Self::get_sender(m2.clone())
            && !Self::depends(m1.clone(), m2.clone())
            && !Self::depends(m2.clone(), m1.clone())
    }
    fn depends(m1: Arc<Self>, m2: Arc<Self>) -> bool {
        Self::get_justifications(m1.clone()).iter().fold(
            Self::get_justifications(m1.clone()).contains(m2.clone()),
            // although this recursion ends supposedly only at genesis message,
            // the trick is the following: it short-circuits while descending on
            // the dependency tree, if it finds a dependent message. when
            // dealing with honest validators, this would return true very fast.
            // all the new derived branches of the justification can be
            // evaluated in parallel, when using par_iter() instead of iter().
            |acc, msg| acc || Self::depends(msg.clone(), m2.clone()),
        )
    }
}

impl<E, S> AbstractMsg for Message<E, S>
where
    E: Estimate,
    S: Sender,
{
    type S = S;
    type E = E;
    fn get_sender(m: Arc<Self>) -> Option<Self::S> {
        m.sender.clone()
    }
    fn get_estimate(m: Arc<Self>) -> Option<Self::E> {
        m.estimate.clone()
    }
    fn get_justifications(m: Arc<Self>) -> Justification<Self> {
        m.justifications.clone()
    }
}

// what happens if in the justification of one of the messages theres a message
// that is newer than the one referred to in the current justification?

// what happens if a sender does not reference his latest message, but
// references a msg that references his last message (this wouldnt be an
// equivocation)

impl<E, S> Hash for Message<E, S>
where
    E: Estimate,
    S: Sender,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.sender.hash(state);
        self.justifications.hash(state);
        self.estimate.hash(state); // the hash of the msg does NOT depend on the estimate
    }
}

impl<E, S> PartialEq for Message<E, S>
where
    E: Estimate,
    S: Sender,
{
    fn eq(&self, other: &Message<E, S>) -> bool {
        self.sender == other.sender
            && self.justifications == other.justifications
            && self.estimate == other.estimate
    }
}

impl<E, S> Debug for Message<E, S>
where
    E: Estimate,
    S: Sender,
{
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(
            f,
            "Message {{ sender: {}}} -> {:?}",
            self.sender.clone().expect("Sender is a None"), // TODO: handle this
            self.justifications
        )
    }
}

pub trait Sender: Hash + Clone + Ord + Eq + Default + Display + Debug {}

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

struct FaultyInsertResult<S: Sender> {
    success: bool,
    msg_fault_weight: WeightUnit,
    weights: Weights<S>,
}

#[derive(Debug, Clone)]
struct Weights<S: Sender> {
    state_fault_weight: WeightUnit,
    senders_weights: Arc<HashMap<S, WeightUnit>>,
    thr: WeightUnit,
}

#[derive(Eq, Ord, PartialOrd, PartialEq, Clone, Default, Hash)]
pub struct Justification<M: AbstractMsg>(BTreeSet<Arc<M>>);

impl<M: AbstractMsg> Justification<M> {
    // re-exports from BTreeSet
    fn new() -> Self {
        Justification(BTreeSet::new())
    }
    fn iter(&self) -> Iter<Arc<M>> {
        self.0.iter()
    }
    fn insert(&mut self, msg: Arc<M>) -> bool {
        self.0.insert(msg.clone())
    }
    fn contains(&self, msg: Arc<M>) -> bool {
        self.0.contains(&msg.clone())
    }
    fn remove(&mut self, msg: Arc<M>) -> bool {
        self.0.remove(&msg.clone())
    }
    fn len(&self) -> usize {
        self.0.len()
    }

    // custom
}

impl<M: AbstractMsg> Justification<M> {
    // fn equivocates(&self, msg: &'m Message<'m, E>) -> bool {
    //     self.latest_msgs
    //         .iter()
    //         .fold(false, |acc, m| acc || Message::equivocates(m, msg))
    // }

    // get the additional fault weight to be added to the state when inserting
    // msg to the state / justification
    fn get_msg_fault_weight_overhead(
        &self,
        msg: Arc<M>,
        senders_weights: Arc<HashMap<M::S, WeightUnit>>,
    ) -> Option<WeightUnit> {
        self.iter().fold(Some(WeightUnit::ZERO), |acc, m| {
            if M::equivocates(m.clone(), msg.clone()) {
                M::get_sender(m.clone())
                    .and_then(|sender| senders_weights.get(&sender))
                    .and_then(|weight| acc.and_then(|acc| Some(acc + weight)))
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
        msg: Arc<M>,
        // FIXME: not sure about the following lifetime, i believe it can be shorter
        weights: Weights<M::S>,
    ) -> FaultyInsertResult<M::S> {
        // if it fails to unwrap, nan ends up in the else branch
        let msg_fault_weight =
            self.get_msg_fault_weight_overhead(
                msg.clone(),
                weights.senders_weights.clone(),
            ).unwrap_or(f64::NAN);

        let new_fault_weight = weights.state_fault_weight + msg_fault_weight;

        // no conflicts, msg added to the set
        if WeightUnit::is_zero(&msg_fault_weight) {
            FaultyInsertResult {
                success: self.insert(msg),
                msg_fault_weight,
                weights,
            }
        }
        else if new_fault_weight <= weights.thr {
            let success = self.insert(msg);
            println!("passed 1");
            let weights = if success {
                Weights {
                    state_fault_weight: new_fault_weight,
                    ..weights
                }
            }
            else {
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

impl<M: AbstractMsg> Debug for Justification<M> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{:?}", self)
    }
}

pub trait Estimate: Hash + Clone + Ord + Default + Sized {
    type M: AbstractMsg<E = Self>;
    fn estimator(justifications: &Justification<Self::M>) -> Self;
}

impl Sender for u32 {}

impl Estimate for VoteCount {
    // the estimator just counts votes, which in this case are the unjustified
    // msgs
    type M = Message<Self, u32>;
    fn estimator(justifications: &Justification<Self::M>) -> Self {
        // stub msg w/ no estimate and no sender

        let msg = Message {
            estimate: None,
            sender: None,
            justifications: justifications.clone(),
        };
        // the estimates are actually the original votes of each of the voters /
        // validators
        let votes = Self::get_vote_msgs(Arc::new(msg), HashSet::new());
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

#[derive(Clone, Debug, Eq, Ord, PartialOrd, PartialEq, Hash, Default)]
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

// impl PartialEq for VoteCount {
//     fn eq(&self, other: &VoteCount) -> bool {
//         self.yes == other.yes && self.no == other.no
//     }
// }

impl VoteCount {
    // makes sure nobody adds more than one vote to their unjustified VoteCount
    // object. if they did, their vote is invalid and will be ignored
    fn is_valid_vote(vote: &Option<Self>) -> bool {
        // these two are the only allowed votes (unjustified msgs)
        vote == &Some(VoteCount { yes: 1, no: 0 })
            || vote == &Some(VoteCount { yes: 0, no: 1 })
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

    fn create_vote_msg<'m, S>(sender: S, vote: bool) -> Arc<Message<Self, S>>
    where
        S: Sender,
    {
        let justifications: Justification<Message<Self, S>> =
            Justification::new();
        Arc::new(Message {
            estimate: match vote {
                true => Some(VoteCount { yes: 1, no: 0 }),
                false => Some(VoteCount { yes: 0, no: 1 }),
            },
            sender: Some(sender),
            justifications,
        })
    }

    fn get_vote_msgs<S>(
        msg: Arc<Message<Self, S>>,
        acc: HashSet<Message<Self, S>>,
    ) -> HashSet<Message<Self, S>>
    where
        S: Sender,
    {
        msg.justifications.iter().fold(acc, |mut acc_new, m| {
            match m.justifications.len() {
                0 => {
                    // vote found, vote is a message with 0 justifications
                    // TODO: prevent double vote
                    if Self::is_valid_vote(&m.estimate) {
                        let equivocation = Message {
                            estimate: Self::toggle_vote(&m.estimate),
                            ..(**m).clone() // FIXME: is this OK?
                        };
                        // search for the equivocation of the current msg
                        match acc_new.get(&equivocation) {
                            // remove the equivoted vote, none of the pair
                            // will stay on the set
                            Some(_) => acc_new.remove(&equivocation),
                            // add the vote
                            None => acc_new.insert((**m).clone()),
                        };
                    }
                    acc_new // returns it
                },
                _ => Self::get_vote_msgs(m.clone(), acc_new),
            }
        })
    }
}

fn main() {}

#[cfg(test)]
mod main {
    use std::sync::{Arc};
    use {Justification, Message, AbstractMsg, VoteCount, Weights, WeightUnit};
    use std::collections::{HashMap};

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

        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        let mut j0 = Justification::new();
        assert!(
            j0.faulty_insert(
                v0.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m0 = Message::new(0, j0.clone());

        let mut j1 = Justification::new();
        assert!(
            j1.faulty_insert(
                v0.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );

        assert!(
            j1.faulty_insert(
                m0.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
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

        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());

        let mut j0 = Justification::new();
        assert!(
            j0.faulty_insert(
                v0.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m0 = Message::new(0, j0);
        assert!(
            !Message::depends(v0.clone(), v0_prime.clone()),
            "v0 does NOT depends on v0_prime as they are equivocating"
        );
        assert!(
            !Message::depends(m0.clone(), m0.clone()),
            "m0 does NOT depends on itself directly, by our impl choice"
        );
        assert!(
            !Message::depends(m0.clone(), v0_prime.clone()),
            "m0 depends on v0 directly"
        );
        assert!(
            Message::depends(m0.clone(), v0.clone()),
            "m0 depends on v0 directly"
        );

        let mut j0 = Justification::new();
        assert!(
            j0.faulty_insert(
                v0.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m0 = Message::new(0, j0.clone());

        let mut j1 = Justification::new();
        assert!(
            j1.faulty_insert(
                v0.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );

        assert!(
            j1.faulty_insert(
                m0.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m1 = Message::new(0, j1.clone());
        assert!(
            Message::depends(m1.clone(), m0.clone()),
            "m1 DOES depent on m0"
        );
        assert!(
            !Message::depends(m0.clone(), m1.clone()),
            "but m0 does NOT depend on m1"
        );
        assert!(
            Message::depends(m1.clone(), v0.clone()),
            "m1 depends on v0 through m0"
        );
    }

    #[test]
    fn msg_equivocates() {
        use AbstractMsg;
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = VoteCount::create_vote_msg(1, true);

        let senders_weights =
            Arc::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());

        let mut j0 = Justification::new();
        assert!(
            j0.faulty_insert(
                v0.clone(),
                Weights {
                    senders_weights,
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
        assert!(
            !Message::equivocates(v0.clone(), v0.clone()),
            "should be all good"
        );
        assert!(
            !Message::equivocates(v1.clone(), m0.clone()),
            "should be all good"
        );
        assert!(
            !Message::equivocates(m0.clone(), v1.clone()),
            "should be all good"
        );
        assert!(
            Message::equivocates(v0.clone(), v0_prime.clone()),
            "should be a direct equivocation"
        );
        assert!(
            Message::equivocates(m0.clone(), v0_prime.clone()),
            "should be an indirect equivocation, equivocates to m0 through v0"
        );
    }

    #[test]
    fn faulty_inserts() {
        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = VoteCount::create_vote_msg(1, true);
        let mut j0 = Justification::new();
        assert!(
            j0.faulty_insert(
                v0.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let m0 = Message::new(0, j0);
        let mut j1 = Justification::new();
        assert!(
            j1.faulty_insert(
                v1.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        assert!(
            j1.faulty_insert(
                m0.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        assert!(
            !j1.faulty_insert(
                v0_prime.clone(),
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0
                }
            ).success,
            "$v0_prime$ should conflict with $v0$ through $m0$, and we should reject as our fault tolerance thr is zero"
        );
        assert!(
            j1.clone()
                .faulty_insert(
                    v0_prime.clone(),
                    Weights {
                        senders_weights: senders_weights.clone(),
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
                    v0_prime.clone(),
                    Weights {
                        senders_weights: senders_weights.clone(),
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
                    v0_prime.clone(),
                    Weights {
                        senders_weights: senders_weights.clone(),
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
                    v0_prime.clone(),
                    Weights {
                        senders_weights: senders_weights.clone(),
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
                    v0_prime.clone(),
                    Weights {
                        senders_weights: senders_weights.clone(),
                        state_fault_weight: 1.0,
                        thr: 2.0
                    }
                )
                .success,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should accept this fault as the thr doesnt get crossed for the set"
        );

        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([].iter().cloned().collect());
        // bug found
        assert!(
            !j1.clone()
                .faulty_insert(
                    v0_prime.clone(),
                    Weights {
                        senders_weights: senders_weights.clone(),
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
                    v0_prime.clone(),
                    Weights {
                        senders_weights: senders_weights.clone(),
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
        let senders_weights =
            Arc::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = VoteCount::create_vote_msg(1, true);
        let mut j0 = Justification::new();
        let weights = Weights {
            senders_weights,
            state_fault_weight: 0.0,
            thr: 2.0,
        };
        assert!(j0.faulty_insert(v0, weights.clone()).success);
        let m0 = Message::new(0, j0);
        let mut j1 = Justification::new();
        assert!(j1.faulty_insert(v1, weights.clone()).success);
        assert!(j1.faulty_insert(m0, weights.clone()).success);

        let m1 = Message::new(1, j1.clone());
        assert_eq!(
            m1.estimate.clone().unwrap(),
            VoteCount { yes: 1, no: 1 },
            "should have 1 yes, and 1 no vote, found {:?}",
            m1.estimate
        );

        assert!(j1.faulty_insert(v0_prime, weights.clone()).success,);
        let m1_prime = Message::new(1, j1.clone());
        assert_eq!(
            m1_prime.estimate.clone().unwrap(),
            VoteCount { yes: 1, no: 0 },
            "should have 1 yes, and 0 no vote, found {:?}, the equivocation vote should cancels out the normal vote",
            m1.estimate
        )
    }
}
