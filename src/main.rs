use std::collections::{BTreeSet, HashMap, HashSet};
use std::collections::btree_set::{Iter};
use std::{f64};
use std::hash::{Hash, Hasher};
use std::ops::{Add};
use std::fmt::{Debug, Formatter, Result};
use std::sync::{Arc};
// use std::io::{Error};
extern crate rayon;
use rayon::prelude::*;

pub trait AbstractMsg: Hash + Ord + Clone + Eq + Sync + Send {
    type E: Estimate;
    type S: Sender;
    fn get_sender(Arc<Self>) -> Option<Self::S>;
    fn get_estimate(Arc<Self>) -> Option<Self::E>;
    fn get_justification(Arc<Self>) -> Justification<Self>;
    fn equivocates(m1: Arc<Self>, m2: Arc<Self>) -> bool {
        m1.clone() != m2.clone()
            && Self::get_sender(m1.clone()) == Self::get_sender(m2.clone())
            && !Self::depends(m1.clone(), m2.clone())
            && !Self::depends(m2.clone(), m1.clone())
    }
    fn depends(m1: Arc<Self>, m2: Arc<Self>) -> bool {
        // although the recursion ends supposedly only at genesis message, the
        // trick is the following: it short-circuits while descending on the
        // dependency tree, if it finds a dependent message. when dealing with
        // honest validators, this would return true very fast. all the new
        // derived branches of the justification will be evaluated in parallel.
        // say if a msg is justified by 2 other msgs, then the 2 other msgs will
        // be processed on different threads. this applies recursively, so if
        // each of the 2 msgs have say 3 justifications, then each of the 2
        // threads will spawn 3 new threads to process each of the messages.
        // thus, highly parallelizable. when it shortcuts, because in one thread
        // a dependency was found, all the computation on the other threads will
        // be cancelled, and the function returns true.
        let justification = Self::get_justification(m1);
        justification.contains(&m2.clone())
            || justification
                .par_iter()
                .any(|m1_prime| Self::depends(m1_prime.clone(), m2.clone()))
    }

    /// returns the dag tip-most safe messages. a safe message is defined as one
    /// that was seen by all senders (with non-zero weight in senders_weights)
    /// and all senders saw each other seeing each other messages. the recursion
    /// should be started with an empty HashSets for senders_referred and
    /// safe_msgs. there cant be more new safe messages than senders (for a
    /// constant set of senders)

    // FIXME: this won't work, it has to be a breath first impl and i did deepth
    // first
    fn get_safe_msgs(
        m: Arc<Self>,
        senders: &HashSet<Self::S>,
        mut senders_referred: HashSet<Self::S>,
        safe_ms: HashSet<Arc<Self>>,
    ) -> HashSet<Arc<Self>> {
        Self::get_justification(m.clone())
            .iter().fold(
            safe_ms,
            |mut safe_ms_prime, m_prime| {
                // base case
                if &senders_referred == senders {
                    let _ = safe_ms_prime.insert(m.clone());
                    safe_ms_prime
                }
                else {
                    let _ = Self::get_sender(m_prime.clone())
                        .map(|sender| senders_referred.insert(sender));
                    Self::get_safe_msgs(
                        m_prime.clone(),
                        senders,
                        senders_referred.clone(),
                        safe_ms_prime,
                    )
                }
            },
        )
    }
}
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
    justification: Justification<Message<E, S>>,
}

/*
// TODO start we should make messages lazy. continue this after async-await is better
// documented

enum MsgStatus {
    Unchecked,
    Valid,
    Invalid,
}

struct Msg<E, S>
where
    E: Estimate,
    S: Sender,
{
    status: MsgStatus,
    msg: Future<Item = Arc<Message<E, S>>, Error = Error>,
}
// TODO end
*/

impl<E, S> Message<E, S>
where
    E: Estimate<M = Self>,
    S: Sender,
{
    fn new(sender: S, justification: Justification<Self>) -> Arc<Self> {
        Arc::new(Self {
            estimate: Some(E::estimator(&justification)),
            sender: Some(sender),
            justification,
        })
    }
    fn from_msgs(
        sender: S,
        msgs: Vec<&Arc<Self>>,
        weights: &Weights<S>,
    ) -> Arc<Self> {
        let mut justification = Justification::new();
        for m in msgs {
            assert!(
                justification
                    .faulty_insert(m.clone(), weights.clone())
                    .success
            );
        }
        Self::new(sender, justification)
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
    fn get_justification(m: Arc<Self>) -> Justification<Self> {
        m.justification.clone()
    }
}

impl<E, S> Hash for Message<E, S>
where
    E: Estimate,
    S: Sender,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        let _ = self.sender.hash(state);
        let _ = self.justification.hash(state);
        let _ = self.estimate.hash(state); // the hash of the msg does NOT depend on the estimate
    }
}

impl<E, S> PartialEq for Message<E, S>
where
    E: Estimate,
    S: Sender,
{
    fn eq(&self, other: &Message<E, S>) -> bool {
        self.sender == other.sender
            && self.justification == other.justification
            && self.estimate == other.estimate
    }
}

impl<E, S> Debug for Message<E, S>
where
    E: Estimate,
    S: Sender,
{
    fn fmt(&self, f: &mut Formatter) -> Result {
        let estimate = self.estimate.clone().unwrap();
        write!(
            f,
            "M{:?}({:?}) -> {:?}",
            self.sender.clone().expect("Sender is a None"), // TODO: handle this
            estimate,
            self.justification
        )
    }
}

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {
    /// helper to picks senders with positive weights
    fn get_senders(
        senders_weights: &Arc<HashMap<Self, WeightUnit>>,
    ) -> HashSet<Self> {
        senders_weights
            .iter()
            .filter(|(_, &weight)| weight > WeightUnit::ZERO)
            .map(|(sender, _)| sender.clone())
            .collect()
    }
}

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
    // Re-exports from BTreeSet wrapping M
    fn new() -> Self {
        Justification(BTreeSet::new())
    }
    fn iter(&self) -> Iter<Arc<M>> {
        self.0.iter()
    }
    fn par_iter(&self) -> rayon::collections::btree_set::Iter<Arc<M>> {
        self.0.par_iter()
    }

    fn insert(&mut self, msg: Arc<M>) -> bool {
        self.0.insert(msg.clone())
    }
    fn contains(&self, msg: &Arc<M>) -> bool {
        self.0.contains(msg)
    }
    fn len(&self) -> usize {
        self.0.len()
    }

    // Custom functions

    /// get the additional fault weight to be added to the state when inserting
    /// msg to the state
    fn get_msg_fault_weight_overhead(
        &self,
        msg: Arc<M>,
        senders_weights: Arc<HashMap<M::S, WeightUnit>>,
    ) -> WeightUnit {
        let weight_overheads = self.par_iter().map(|msg_prime| {
            if M::equivocates(msg_prime.clone(), msg.clone()) {
                M::get_sender(msg_prime.clone())
                    .and_then(|sender| senders_weights.get(&sender))
                    .unwrap_or(&f64::NAN)
            }
            else {
                &WeightUnit::ZERO
            }
        });

        weight_overheads.sum()
    }
    /// insert msgs to the Justification, accepting up to $thr$ faults by
    /// sender's weight
    fn faulty_insert(
        &mut self,
        msg: Arc<M>,
        weights: Weights<M::S>,
    ) -> FaultyInsertResult<M::S> {
        let msg_fault_weight = self.get_msg_fault_weight_overhead(
            msg.clone(),
            weights.senders_weights.clone(),
        );

        let new_fault_weight = weights.state_fault_weight + msg_fault_weight;

        // no conflicts, msg added to the set
        if WeightUnit::is_zero(&msg_fault_weight) {
            FaultyInsertResult {
                success: self.insert(msg),
                weights,
            }
        }
        else if new_fault_weight <= weights.thr {
            let success = self.insert(msg);
            let weights = if success {
                Weights {
                    state_fault_weight: new_fault_weight,
                    ..weights
                }
            }
            else {
                weights
            };

            FaultyInsertResult { success, weights }
        }
        // conflicting message NOT added to the set as it crosses the fault
        // weight thr OR get_msg_fault_weight_overhead returned NAN
        else {
            FaultyInsertResult {
                success: false,
                weights,
            }
        }
    }
}

impl<E, S> Debug for Justification<Message<E, S>>
where
    E: Estimate,
    S: Sender,
{
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{:?}", self.0)
    }
}

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug {
    type M: AbstractMsg<E = Self>;
    // TODO: this estimator is good only if there's no external dependency, not
    // good for blockchain consensus
    fn estimator(justification: &Justification<Self::M>) -> Self;
}

impl Sender for u32 {}

impl Estimate for VoteCount {
    // the estimator just counts votes, which in this case are the unjustified
    // msgs
    type M = Message<Self, u32>;
    fn estimator(justification: &Justification<Self::M>) -> Self {
        // stub msg w/ no estimate and no sender

        let msg = Message {
            estimate: None,
            sender: None,
            justification: justification.clone(),
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

/// the value $z$ that, when added to other value $x$ of same type, returns the
/// other value x: $z + x = x$
trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}

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

    fn create_vote_msg<S>(sender: S, vote: bool) -> Arc<Message<Self, S>>
    where
        S: Sender,
    {
        let justification: Justification<Message<Self, S>> =
            Justification::new();
        Arc::new(Message {
            estimate: match vote {
                true => Some(VoteCount { yes: 1, no: 0 }),
                false => Some(VoteCount { yes: 0, no: 1 }),
            },
            sender: Some(sender),
            justification,
        })
    }

    fn get_vote_msgs<S>(
        msg: Arc<Message<Self, S>>,
        acc: HashSet<Message<Self, S>>,
    ) -> HashSet<Message<Self, S>>
    where
        S: Sender,
    {
        msg.justification.iter().fold(acc, |mut acc_new, m| {
            match m.justification.len() {
                0 => {
                    // vote found, vote is a message with 0 justification
                    // TODO: prevent double vote
                    if Self::is_valid_vote(&m.estimate) {
                        let equivocation = Message {
                            estimate: Self::toggle_vote(&m.estimate),
                            ..(**m).clone() // FIXME: is this OK? why 2 levels of indirection?
                        };
                        // search for the equivocation of the current msg
                        match acc_new.get(&equivocation) {
                            // remove the equivoted vote, none of the pair
                            // will stay on the set
                            Some(_) => acc_new.remove(&equivocation),
                            // add the vote
                            None => acc_new.insert((**m).clone()), // FIXME: is this OK?
                        };
                    }
                    acc_new // returns it
                },
                _ => Self::get_vote_msgs(m.clone(), acc_new),
            }
        })
    }
}

fn main() {
    let v0 = VoteCount::create_vote_msg(0, false);
    println!("{:?}", v0);
}

#[cfg(test)]
mod main {
    use std::sync::{Arc};
    use std::collections::{HashMap};
    use super::*;

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
    fn msg_safe() {
        // setup
        use AbstractMsg;
        let sender0 = 0;
        let sender1 = 1;
        let senders_weights: Arc<HashMap<u32, WeightUnit>> = Arc::new(
            [(sender0, 1.0), (sender1, 1.0)].iter().cloned().collect(),
        );
        let weights = Weights {
            senders_weights: senders_weights.clone(),
            state_fault_weight: 0.0,
            thr: 0.0,
        };
        let senders = &Sender::get_senders(&senders_weights);

        // sender0       v0-----m0         m2
        //                       \        /
        // sender1                \--m1--/
        let v0 = VoteCount::create_vote_msg(sender0, false);
        let safe_msgs = AbstractMsg::get_safe_msgs(
            v0.clone(),
            senders,
            HashSet::new(),
            HashSet::new(),
        );
        assert_eq!(safe_msgs.len(), 0, "only sender0 saw v0");

        let m0 = Message::from_msgs(sender0, vec![&v0], &weights);
        let safe_msgs = AbstractMsg::get_safe_msgs(
            m0.clone(),
            senders,
            HashSet::new(),
            HashSet::new(),
        );
        assert_eq!(safe_msgs.len(), 0, "only sender0 saw v0 and m0");

        let m1 = Message::from_msgs(sender1, vec![&m0], &weights);
        let safe_msgs = AbstractMsg::get_safe_msgs(
            m1.clone(),
            senders,
            HashSet::new(),
            HashSet::new(),
        );
        assert_eq!(
            safe_msgs.len(),
            0,
            "both sender0 and sender1 saw v0 and m0, but sender0 hasn't
necessarly seen sender1 seeing v0 and m0, thus not yet safe"
        );

        let m2 = Message::from_msgs(sender0, vec![&m1], &weights);
        let safe_msgs = AbstractMsg::get_safe_msgs(
            m2.clone(),
            senders,
            HashSet::new(),
            HashSet::new(),
        );
        assert_eq!(
            safe_msgs,
            [m0.clone()].iter().cloned().collect(),
            "both sender0 and sender1 saw v0 and m0, and additionally both
parties saw each other seing v0 and m0, m0 (and all its dependencies) are final"
        );






        // 2-lane dag
        let v0 = VoteCount::create_vote_msg(sender0, false);
        let v1 = VoteCount::create_vote_msg(sender1, false);
        let m0 = Message::from_msgs(sender0, vec![&v0, &v1], &weights);
        let safe_msgs = AbstractMsg::get_safe_msgs(
            m0.clone(),
            senders,
            HashSet::new(),
            HashSet::new(),
        );
        assert_eq!(safe_msgs.len(), 0, "only sender0 saw v0, v1 and m0");

        let m1 = Message::from_msgs(sender1, vec![&m0], &weights);
        let safe_msgs = AbstractMsg::get_safe_msgs(
            m1.clone(),
            senders,
            HashSet::new(),
            HashSet::new(),
        );
        assert_ne!(safe_msgs.len(), 0);

        assert_eq!(
            safe_msgs,
            [v1].iter().cloned().collect(),
            "both sender0 and sender1 saw v0, v1 and m0, but sender0 hasn't
necessarly seen sender1 seeing v0 and m0, just v1 is safe"
        );

        let m2 = Message::from_msgs(sender0, vec![&m1], &weights);
        let safe_msgs = AbstractMsg::get_safe_msgs(
            m2.clone(),
            senders,
            HashSet::new(),
            HashSet::new(),
        );
        assert_eq!(
            safe_msgs,
            [m1].iter().cloned().collect(),
            "both sender0 and sender1 saw v0 and m0, and additionally both
parties saw each other seing v0 and m0, safe"
        );
    }

    #[test]
    fn debug() {
        let v0 = VoteCount::create_vote_msg(0, false);
        println!("{:?}", v0);
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
                .weights
                .state_fault_weight,
            1.0,
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept
this fault as it doesnt cross the fault threshold for the set, and thus the
state_fault_weight should be incremented to 1.0"
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

        assert!(j1.faulty_insert(v0_prime, weights.clone()).success);
        let m1_prime = Message::new(1, j1.clone());
        assert_eq!(
            m1_prime.estimate.clone().unwrap(),
            VoteCount { yes: 1, no: 0 },
            "should have 1 yes, and 0 no vote, found {:?}, the equivocation vote should cancels out the normal vote",
            m1.estimate
        )
    }
    #[test]
    fn get_senders() {
        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            Sender::get_senders(&senders_weights),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with valid, positive weight"
        );

        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 0.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            Sender::get_senders(&senders_weights),
            [1, 2].iter().cloned().collect(),
            "should exclude senders with 0 weight"
        );

        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 1.0), (1, -1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            Sender::get_senders(&senders_weights),
            [0, 2].iter().cloned().collect(),
            "should exclude senders with negative weight"
        );

        let senders_weights: Arc<HashMap<u32, WeightUnit>> = Arc::new(
            [(0, f64::NAN), (1, 1.0), (2, 1.0)]
                .iter()
                .cloned()
                .collect(),
        );
        assert_eq!(
            Sender::get_senders(&senders_weights),
            [1, 2].iter().cloned().collect(),
            "should exclude senders with NAN weight"
        );

        let senders_weights: Arc<HashMap<u32, WeightUnit>> = Arc::new(
            [(0, f64::INFINITY), (1, 1.0), (2, 1.0)]
                .iter()
                .cloned()
                .collect(),
        );
        assert_eq!(
            Sender::get_senders(&senders_weights),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with INFINITY weight"
        );
    }
}
