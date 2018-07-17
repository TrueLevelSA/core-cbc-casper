
use std::collections::{BTreeSet, HashMap, HashSet};
use std::collections::btree_set::{Iter};
use std::{f64};
use std::fmt::{Debug, Formatter, Result};
use std::sync::{Arc};
// use std::io::{Error};
use message::{AbstractMsg, Message};
use rayon::collections::btree_set::Iter as ParIter;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use sender::{Sender};
use estimate::{Estimate};
use weight_unit::{WeightUnit};
use zero::{Zero};

#[derive(Eq, Ord, PartialOrd, PartialEq, Clone, Default, Hash)]
pub struct Justification<M: AbstractMsg>(BTreeSet<Arc<M>>);

impl<M: AbstractMsg> Justification<M> {
    // Re-exports from BTreeSet wrapping M
    pub fn new() -> Self {
        Justification(BTreeSet::new())
    }
    pub fn iter(&self) -> Iter<Arc<M>> {
        self.0.iter()
    }
    pub fn par_iter(&self) -> ParIter<Arc<M>> {
        self.0.par_iter()
    }
    pub fn contains(&self, msg: &Arc<M>) -> bool {
        self.0.contains(msg)
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    fn insert(&mut self, msg: Arc<M>) -> bool {
        self.0.insert(msg)
    }

    // Custom functions

    /// get the additional equivocators upon insertion of msg to the state. note
    /// that if equivocator is a recurrent equivocator, it will be found again
    /// here. i believe the weight of an equivocator has to be set to ZERO
    /// immediately upon finding an equivocation
    fn get_equivocators(&self, msg_new: &Arc<M>) -> HashSet<M::S> {
        self.par_iter()
            .filter_map(|msg_old| {
                if M::equivocates(&msg_old, &msg_new) {
                    let equivocator = M::get_sender(&msg_old);
                    Some(equivocator.clone())
                }
                else {
                    None
                }
            })
            .collect()
    }

    /// insert msgs to the Justification, accepting up to $thr$ faults by weight
    pub fn faulty_insert(
        &mut self,
        msg: &Arc<M>,
        weights: Weights<M::S>,
    ) -> FaultyInsertResult<M::S> {
        let equivocators = self.get_equivocators(msg);
        let msg_fault_weight_overhead = equivocators.iter().fold(
            WeightUnit::ZERO,
            |acc, equivocator| {
                acc + SenderWeight::get_weight(&weights.senders_weights, equivocator)
            },
        );

        let new_fault_weight =
            weights.state_fault_weight + msg_fault_weight_overhead;

        if new_fault_weight <= weights.thr {
            let success = self.insert(msg.clone());
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
                weights,
                equivocators,
            }
        }
        // conflicting message NOT added to the set as it crosses the fault
        // weight thr OR msg_fault_weight is NAN (from the unwrap)
        else {
            FaultyInsertResult {
                success: false,
                weights,
                equivocators,
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


pub struct FaultyInsertResult<S: Sender> {
    pub success: bool,
    pub weights: Weights<S>,
    pub equivocators: HashSet<S>,
}

#[derive(Debug, Clone)]
pub struct Weights<S: Sender> {
    senders_weights: Arc<HashMap<S, WeightUnit>>,
    state_fault_weight: WeightUnit,
    thr: WeightUnit,
}
impl<S: Sender> Weights<S> {
    pub fn new(
        senders_weights: Arc<HashMap<S, WeightUnit>>,
        state_fault_weight: WeightUnit,
        thr: WeightUnit,
    ) -> Self {
        Weights {
            state_fault_weight,
            senders_weights,
            thr,
        }
    }
}

struct SenderWeight<S: Sender>(Arc<HashMap<S, WeightUnit>>);

impl<S: Sender> SenderWeight<S> {
    /// picks senders with positive weights
    fn get_senders(
        senders_weights: &Arc<HashMap<S, WeightUnit>>,
    ) -> HashSet<S> {
        senders_weights
            .iter()
            .filter(|(_, &weight)| weight > WeightUnit::ZERO)
            .map(|(sender, _)| sender.clone())
            .collect()
    }

    fn get_weight(
        senders_weights: &Arc<HashMap<S, WeightUnit>>,
        sender: &S,
    ) -> WeightUnit {
        senders_weights.get(sender).unwrap_or(&f64::NAN).clone()
    }

    fn into_relative_weights(
        senders_weights: &Arc<HashMap<S, WeightUnit>>,
    ) -> Arc<HashMap<S, WeightUnit>> {
        let iterator = senders_weights
            .iter()
            .filter(|(_, &weight)| weight > WeightUnit::ZERO);

        let total_weight: WeightUnit = iterator
            .clone()
            .fold(WeightUnit::ZERO, |acc, (_, weight)| acc + weight);

        Arc::new(
            iterator
                .map(|(sender, weight)| {
                    (sender.clone(), weight.clone() / total_weight)
                })
                .collect(),
        )
    }
}

#[cfg(test)]
mod message {
    use vote_count::{VoteCount};
    use super::*;
    #[test]
    fn faulty_inserts() {
        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = &VoteCount::create_vote_msg(1, true);
        let mut j0 = Justification::new();
        assert!(
            j0.faulty_insert(
                v0,
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        let estimate = VoteCount::estimator(&j0);
        let m0 = &Message::new(0, j0, Some(estimate));
        let mut j1 = Justification::new();
        assert!(
            j1.faulty_insert(
                v1,
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        assert!(
            j1.faulty_insert(
                m0,
                Weights {
                    senders_weights: senders_weights.clone(),
                    state_fault_weight: 0.0,
                    thr: 0.0,
                }
            ).success
        );
        assert!(
            !j1.faulty_insert(
                v0_prime,
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
                    v0_prime,
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
                    v0_prime,
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
                    v0_prime,
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
                    v0_prime,
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
                    v0_prime,
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
                    v0_prime,
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
                    v0_prime,
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
}
