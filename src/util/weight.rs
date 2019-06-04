use std::collections::{HashMap, HashSet};
use std::sync::{Arc, LockResult, RwLock, RwLockReadGuard, RwLockWriteGuard};

use traits::{Sender, Zero};

pub type WeightUnit = f64;

impl Zero<WeightUnit> for WeightUnit {
    const ZERO: Self = 0.0f64;

    fn is_zero(val: &Self) -> bool {
        val > &-::std::f64::EPSILON && val < &::std::f64::EPSILON
    }
}

// RwLock locks only before writing, while Mutex locks to both read and write

#[derive(Clone, Default, Debug)]
pub struct SendersWeight<S: Sender>(Arc<RwLock<HashMap<S, WeightUnit>>>);

impl<S: Sender> SendersWeight<S> {
    /// creates a new SendersWeight from a HashMap
    pub fn new(senders_weight: HashMap<S, WeightUnit>) -> Self {
        SendersWeight(Arc::new(RwLock::new(senders_weight)))
    }

    /// same as RwLock read() function
    /// basically locks the Rwlock with read access
    /// insert and senders?
    fn read(&self) -> LockResult<RwLockReadGuard<HashMap<S, WeightUnit>>> {
        self.0.read()
    }

    /// same as RwLock write() function
    /// basically locks the RwLock with write access
    fn write(&self) -> LockResult<RwLockWriteGuard<HashMap<S, WeightUnit>>> {
        self.0.write()
    }

    /// returns success of insertion. failure happens if cannot unwrap self
    pub fn insert(&mut self, k: S, v: WeightUnit) -> bool {
        self.write()
            .ok()
            .map(|mut h| {
                h.insert(k, v);
                true
            })
            .unwrap_or(false)
    }

    /// picks senders with positive weights
    pub fn senders(&self) -> Result<HashSet<S>, &'static str> {
        self.read()
            .map_err(|_| "Can't unwrap SendersWeight")
            .map(|senders_weight| {
                senders_weight
                    .iter()
                    .filter_map(|(sender, &weight)| {
                        if weight > WeightUnit::ZERO {
                            Some(sender.clone())
                        } else {
                            None
                        }
                    })
                    .collect()
            })
    }

    /// Gets the weight of the sender
    /// Returns an Error in case there is a reading error
    /// or the sender does not exist
    pub fn weight(&self, sender: &S) -> Result<WeightUnit, &'static str> {
        self.read()
            .map_err(|_| "Can't unwrap SendersWeight")
            .and_then(|weights| match weights.get(sender) {
                Some(weight) => Ok(weight.clone()),
                None => Err("Could not find sender"),
            })
    }

    /// returns the total weight of all the senders
    pub fn sum_weight_senders(&self, senders: &HashSet<S>) -> WeightUnit {
        senders.iter().fold(WeightUnit::ZERO, |acc, sender| {
            acc + self.weight(sender).unwrap_or(::std::f64::NAN)
        })
    }

    pub fn sum_all_weights(&self) -> WeightUnit {
        if let Ok(senders) = self.senders() {
            self.sum_weight_senders(&senders)
        } else {
            ::std::f64::NAN
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn senders() {
        let senders_weights =
            SendersWeight::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            SendersWeight::senders(&senders_weights).unwrap(),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with valid, positive weight"
        );

        let senders_weights =
            SendersWeight::new([(0, 0.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            SendersWeight::senders(&senders_weights).unwrap(),
            [1, 2].iter().cloned().collect(),
            "should exclude senders with 0 weight"
        );

        let senders_weights =
            SendersWeight::new([(0, 1.0), (1, -1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            SendersWeight::senders(&senders_weights).unwrap(),
            [0, 2].iter().cloned().collect(),
            "should exclude senders with negative weight"
        );

        let senders_weights = SendersWeight::new(
            [(0, ::std::f64::NAN), (1, 1.0), (2, 1.0)]
                .iter()
                .cloned()
                .collect(),
        );
        assert_eq!(
            SendersWeight::senders(&senders_weights).unwrap(),
            [1, 2].iter().cloned().collect(),
            "should exclude senders with NAN weight"
        );

        let senders_weights = SendersWeight::new(
            [(0, ::std::f64::INFINITY), (1, 1.0), (2, 1.0)]
                .iter()
                .cloned()
                .collect(),
        );
        assert_eq!(
            SendersWeight::senders(&senders_weights).unwrap(),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with INFINITY weight"
        );
    }
}
