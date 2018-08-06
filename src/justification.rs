use std::collections::{BTreeSet, HashSet, HashMap};
use std::collections::btree_set::{Iter};
use std::fmt::{Debug, Formatter, Result};
// use std::io::{Error};
use message::{AbstractMsg, Message};
use rayon::collections::btree_set::Iter as ParIter;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use weight_unit::{WeightUnit};
use traits::{Zero, Sender};
use senders_weight::SendersWeight;

#[derive(Eq, Ord, PartialOrd, PartialEq, Clone, Default, Hash)]
pub struct Justification<M: AbstractMsg>(BTreeSet<M>);

impl<M: AbstractMsg> Justification<M> {
    // Re-exports from BTreeSet wrapping M
    pub fn new() -> Self {
        Justification(BTreeSet::new())
    }
    pub fn iter(&self) -> Iter<M> {
        self.0.iter()
    }
    pub fn par_iter(&self) -> ParIter<M> {
        self.0.par_iter()
    }
    pub fn contains(&self, msg: &M) -> bool {
        self.0.contains(msg)
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn insert(&mut self, msg: M) -> bool {
        self.0.insert(msg)
    }
    fn head(&self) -> Option<&M> {
        self.0.iter().next()
    }
    // Custom functions

    /// get the additional equivocators upon insertion of msg to the state. note
    /// that if equivocator is a recurrent equivocator, it will be found again
    /// here. i believe the weight of an equivocator has to be set to ZERO
    /// immediately upon finding an equivocation
    fn get_equivocators(&self, msg_new: &M) -> HashSet<M::Sender> {
        self.par_iter()
            .filter_map(|msg_old| {
                if msg_old.equivocates(&msg_new) {
                    let equivocator = msg_old.get_sender();
                    Some(equivocator.clone())
                }
                else {
                    None
                }
            })
            .collect()
    }

    /// insert msgs to the Justification, accepting up to $thr$ faults by
    /// weight, returns success=true if at least one msg of the set gets
    /// successfully included to the justification
    pub fn faulty_inserts(
        &mut self,
        msgs: HashSet<&M>,
        weights: &Weights<M::Sender>,
    ) -> FaultyInsertResult<M::Sender> {
        /// get msgs and fault weight overhead and equivocators overhead sorted
        /// by fault weight overhead
        fn get_msgs_sorted_by_faultweight<'z, M: AbstractMsg>(
            justification: &Justification<M>,
            Weights {
                senders_weights,
                equivocators,
                ..
            }: &Weights<M::Sender>,
            msgs: HashSet<&'z M>,
        ) -> Vec<&'z M> {
            let mut msgs_sorted_by_faultw: Vec<_> = msgs
                .iter()
                .enumerate()
                .filter_map(|(outer_i, &msg)| {
                    // equivocations in relation to state
                    let state_equvctrs: HashSet<_> =
                        justification.get_equivocators(msg);

                    // equivocations present within the current latest_msgs set that
                    // we're trying to insert to the state
                    let pairwise_equivocators: HashSet<_> = msgs
                        .iter()
                    // ensures we check only once per pair [(a, b)] and not
                    // [(a, b), (b, a)]
                        .skip(outer_i)
                        .filter_map(|m| {
                            if m.equivocates(msg) { Some(m.get_sender()) }
                            else { None }
                        })
                        .collect();

                    let msg_equivocators: HashSet<_> = state_equvctrs
                        .union(&pairwise_equivocators)
                    // take only the equivocators that are not yet on the
                    // equivocator set as the others already have their
                    // weight counted into the state fault count
                        .filter(|equivocator| !equivocators.contains(equivocator))
                        .cloned()
                        .collect();
                    let msg_faultweight_overhead =
                        senders_weights.sum_weight_senders(&msg_equivocators);
                    // sum_weight_senders returns nan if a sender is not found
                    if msg_faultweight_overhead.is_nan() {
                        None
                    }
                    else {
                        Some((msg, msg_faultweight_overhead))
                    }
                })
                .collect();
            let _ = msgs_sorted_by_faultw.sort_unstable_by(
                |(_, w0), (_, w1)| w0.partial_cmp(w1).unwrap(),
            );

            // return a Vec<AbstractMsg>
            msgs_sorted_by_faultw
                .iter()
                .map(|(m, _)| m)
                .cloned()
                .collect()
        }

        // do the actual insertions to the state
        get_msgs_sorted_by_faultweight(&self, &weights, msgs)
            .iter()
            .fold(
                FaultyInsertResult {
                    success: false,
                    weights: weights.clone(),
                },
                |acc, &msg| {
                    let FaultyInsertResult { success, weights } =
                        self.faulty_insert(msg, &acc.weights);
                    FaultyInsertResult {
                        success: acc.success || success,
                        weights,
                    }
                },
            )
    }

    pub fn faulty_insert(
        &mut self,
        msg: &M,
        weights: &Weights<M::Sender>,
    ) -> FaultyInsertResult<M::Sender> {
        let weights = weights.clone();
        let msg_equivocators_overhead: HashSet<_> = self.get_equivocators(msg)
            .iter()
        // take only the msg_eoquivocators_overhead that are not yet on the
        // equivocator set as the others already have their weight counted into
        // the state fault count
            .filter(|equivocator| !weights.equivocators.contains(equivocator))
            .cloned()
            .collect();
        let msg_fault_weight_overhead = weights
            .senders_weights
            .sum_weight_senders(&msg_equivocators_overhead);
        let new_fault_weight =
            weights.state_fault_weight + msg_fault_weight_overhead;
        let equivocators = weights
            .equivocators
            .union(&msg_equivocators_overhead)
            .cloned()
            .collect();

        if new_fault_weight <= weights.thr {
            let success = self.insert(msg.clone());
            let weights = if success {
                Weights {
                    state_fault_weight: new_fault_weight,
                    equivocators,
                    ..weights
                }
            }
            else {
                Weights { ..weights }
            };

            FaultyInsertResult { success, weights }
        }
        // conflicting message NOT added to the set as it crosses the fault
        // weight thr OR msg_fault_weight_overhead is NAN (from the unwrap)
        else {
            FaultyInsertResult {
                success: false,
                weights: Weights {
                    // equivocators,
                    ..weights
                },
            }
        }
    }
    /// get cum weights until reaching safe_msg
    pub fn get_children_weights(
        &self,
        finalized_msg: Option<&M>,
        senders_weights: &SendersWeight<M::Sender>,
        all_senders: &HashSet<M::Sender>,
    ) -> HashMap<M, WeightUnit> {
        fn recursor<M>(
            m: &M,
            finalized_msg: Option<&M>, // if None, runs all the way to genesis msgs
            senders_weights: &SendersWeight<M::Sender>,
            all_senders: &HashSet<M::Sender>,
            mut senders_referred: HashSet<M::Sender>,
            initial_weight: WeightUnit,
        ) -> WeightUnit
        where
            M: AbstractMsg,
        {
            m.get_justification().iter().fold(
                initial_weight,
                |weight_referred, m_prime| {
                    // base case
                    if finalized_msg
                        .and_then(|finalized_msg| {
                            Some(
                                finalized_msg == m_prime
                                    || !m_prime.depends(finalized_msg), // TODO: check if needed
                            )
                        })
                        .unwrap_or(false)
                    {
                        weight_referred
                    }
                    else {
                        let sender_current = m_prime.get_sender();
                        let weight_referred = if senders_referred
                            .insert(sender_current.clone())
                        {
                            weight_referred
                                + senders_weights
                                    .get_weight(&sender_current)
                                    .unwrap_or(WeightUnit::ZERO)
                        }
                        else {
                            weight_referred
                        };

                        recursor(
                            m_prime,
                            finalized_msg,
                            senders_weights,
                            all_senders,
                            senders_referred.clone(),
                            weight_referred,
                        )
                    }
                },
            )
        };
        // initial state, trigger recursion
        let senders_referred: HashSet<M::Sender> = [].iter().cloned().collect();
        let initial_weight = WeightUnit::ZERO;
        self.iter()
            .map(|m| {
                (
                    m.clone(),
                    recursor(
                        m,
                        finalized_msg,
                        senders_weights,
                        all_senders,
                        senders_referred.clone(),
                        initial_weight,
                    ),
                )
            })
            .collect()
    }
}

impl<M: AbstractMsg> Debug for Justification<M> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{:?}", self.0)
    }
}

// FIXME: success should probably be out of this struct, as this struct can be
// used to keep track of state cummulatively and success is related to a single
// insertion
pub struct FaultyInsertResult<S: Sender> {
    pub success: bool,
    pub weights: Weights<S>,
    // pub equivocators: HashSet<S>,
}

// FIXME: this became more than Weights, should find a better name, or break up in parts
#[derive(Debug, Clone)]
pub struct Weights<S: Sender> {
    senders_weights: SendersWeight<S>,
    state_fault_weight: WeightUnit,
    thr: WeightUnit,
    equivocators: HashSet<S>, // FIXME: put it here as its needed on the same context as
}

impl<S: Sender> Weights<S> {
    pub fn new(
        senders_weights: SendersWeight<S>,
        state_fault_weight: WeightUnit,
        thr: WeightUnit,
        equivocators: HashSet<S>,
    ) -> (Self) {
        Weights {
            senders_weights,
            equivocators,
            state_fault_weight,
            thr,
        }
    }
    pub fn get_senders_weights(&self) -> &SendersWeight<S> {
        &self.senders_weights
    }
}

#[cfg(test)]
mod justification {
    use vote_count::{VoteCount};
    use super::*;
    #[test]
    fn faulty_inserts_sorted() {
        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, 2.0), (2, 3.0)].iter().cloned().collect(),
        );

        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true);
        let v1 = &VoteCount::create_vote_msg(1, true);
        let v1_prime = &VoteCount::create_vote_msg(1, false);
        let v2 = &VoteCount::create_vote_msg(2, true);
        let v2_prime = &VoteCount::create_vote_msg(2, false); // equivocating vote
        let weights = Weights {
            senders_weights: senders_weights.clone(),
            state_fault_weight: 0.0,
            thr: 3.0,
            equivocators: HashSet::new(),
        };
        let (m0, weights) = &Message::from_msgs(
            0,
            vec![v2, v2_prime, v1, v1_prime, v0, v0_prime],
            None,
            &weights,
            None as Option<VoteCount>,
        );
        let mut rhs = Justification::new();
        rhs.insert(v0.clone());
        rhs.insert(v0_prime.clone());
        rhs.insert(v1.clone());
        rhs.insert(v1_prime.clone());
        rhs.insert(v2.clone());
        assert_eq!(m0.get_justification(), &rhs);
        assert_eq!(weights.state_fault_weight, 3.0);
    }
    #[test]
    #[ignore]
    fn faulty_inserts() {
        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        );
        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = &VoteCount::create_vote_msg(1, true);
        let mut j0 = Justification::new();
        let weights = Weights {
            senders_weights: senders_weights.clone(),
            state_fault_weight: 0.0,
            thr: 0.0,
            equivocators: HashSet::new(),
        };
        assert!(
            j0.faulty_inserts([v0].iter().cloned().collect(), &weights)
                .success
        );
        let (m0, _weights) = &Message::from_msgs(
            0,
            vec![v0],
            None,
            &weights,
            None as Option<VoteCount>,
        );
        // let m0 = &Message::new(0, justification, estimate);
        let mut j1 = Justification::new();
        assert!(
            j1.faulty_inserts(
                vec![v1].iter().cloned().collect(),
                &Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                    equivocators: HashSet::new(),
                }
            ).success
        );
        assert!(
            j1.faulty_inserts(
                vec![m0].iter().cloned().collect(),
                &Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                    equivocators: HashSet::new(),
                }
            ).success
        );
        assert!(
            !j1.faulty_inserts(
                vec![v0_prime].iter().cloned().collect(),
                &Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                    equivocators: HashSet::new(),
                }
            ).success,
            "$v0_prime$ should conflict with $v0$ through $m0$, and we should reject as our fault tolerance thr is zero"
        );
        assert!(
            j1.clone()
                .faulty_inserts(
                    vec![v0_prime].iter().cloned().collect(),
                    &Weights {
                        senders_weights: senders_weights.clone(),
                        state_fault_weight: 0.0,
                        thr: 1.0,
                        equivocators: HashSet::new(),
                    }
                )
                .success,
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set"
        );

        assert_eq!(
            j1.clone()
                .faulty_inserts(
                    vec![v0_prime].iter().cloned().collect(),
                    &Weights {
                        senders_weights: senders_weights.clone(),
                        state_fault_weight: 0.0,
                        thr: 1.0,
                        equivocators: HashSet::new(),
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
                .faulty_inserts(
                    vec![v0_prime].iter().cloned().collect(),
                    &Weights {
                        senders_weights: senders_weights.clone(),
                        state_fault_weight: 0.1,
                        thr: 1.0,
                        equivocators: HashSet::new(),
                    }
                )
                .success,
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should not accept this fault as the fault threshold gets crossed for the set"
        );

        assert_eq!(
            j1.clone()
                .faulty_inserts(
                    vec![v0_prime].iter().cloned().collect(),
                    &Weights {
                        senders_weights: senders_weights.clone(),
                        state_fault_weight: 0.1,
                        thr: 1.0,
                        equivocators: HashSet::new(),
                    }
                )
                .weights.state_fault_weight,
            0.1,
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should NOT accept this fault as the fault threshold gets crossed for the set, and thus the state_fault_weight should not be incremented"
        );

        assert!(
            j1.clone()
                .faulty_inserts(
                    vec![v0_prime].iter().cloned().collect(),
                    &Weights {
                        senders_weights: senders_weights.clone(),
                        state_fault_weight: 1.0,
                        thr: 2.0,
                        equivocators: HashSet::new(),
                    }
                )
                .success,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should accept this fault as the thr doesnt get crossed for the set"
        );

        let senders_weights = SendersWeight::new([].iter().cloned().collect());
        // bug found
        assert!(
            !j1.clone()
                .faulty_inserts(
                    vec![v0_prime].iter().cloned().collect(),
                    &Weights {
                        senders_weights: senders_weights.clone(),
                        state_fault_weight: 1.0,
                        thr: 2.0,
                        equivocators: HashSet::new(),
                    }
                )
                .success,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity"
        );

        assert_eq!(
            j1.clone()
                .faulty_inserts(
                    vec![v0_prime].iter().cloned().collect(),
                    &Weights {
                        senders_weights: senders_weights.clone(),
                        state_fault_weight: 1.0,
                        thr: 2.0,
                        equivocators: HashSet::new(),
                    }
                )
                .weights.state_fault_weight,
            1.0,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity, and thus the state_fault_weight should be unchanged"
        );
    }
}
