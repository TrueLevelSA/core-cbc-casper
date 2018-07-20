use weight_unit::WeightUnit;
use std::collections::{HashMap, HashSet};
use traits::{Zero, Sender};
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard, LockResult};

// RwLock locks only before writing, while Mutex locks to both read and write

#[derive(Clone, Default, Debug)]
pub struct SendersWeight<S: Sender>(Arc<RwLock<HashMap<S, WeightUnit>>>);

impl<S: Sender> SendersWeight<S> {
    pub fn new(senders_weight: HashMap<S, WeightUnit>) -> Self {
        SendersWeight(Arc::new(RwLock::new(senders_weight)))
    }

    fn read(&self) -> LockResult<RwLockReadGuard<HashMap<S, WeightUnit>>> {
        self.0.read()
    }

    fn write(&self) -> LockResult<RwLockWriteGuard<HashMap<S, WeightUnit>>> {
        self.0.write()
    }

    /// picks senders with positive weights
    pub fn get_senders(&self) -> HashSet<S> {
        self.read()
            .unwrap()
            .iter()
            .filter_map(|(sender, &weight)| {
                if weight > WeightUnit::ZERO {
                    Some(sender.clone())
                }
                else {
                    None
                }
            })
            .collect()
    }

    pub fn get_weight(&self, sender: &S) -> Option<WeightUnit> {
        self.read()
            .unwrap()
            .get(sender)
            .and_then(|weight| Some(weight.clone()))
    }

    pub fn into_relative_weights(&self) -> Self {
        let senders_weights = self.read().unwrap();

        let iterator = senders_weights
            .iter()
            .filter(|(_, &weight)| weight > WeightUnit::ZERO);

        let total_weight: WeightUnit = iterator
            .clone()
            .fold(WeightUnit::ZERO, |acc, (_, weight)| acc + weight);

        SendersWeight::new(
            iterator
                .map(|(sender, weight)| {
                    (sender.clone(), weight.clone() / total_weight)
                })
                .collect(),
        )
    }
}

#[cfg(test)]
mod sender_weight {
    use super::*;

    #[test]
    fn get_senders() {
        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        );
        assert_eq!(
            SendersWeight::get_senders(&senders_weights),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with valid, positive weight"
        );

        let senders_weights = SendersWeight::new(
            [(0, 0.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        );
        assert_eq!(
            SendersWeight::get_senders(&senders_weights),
            [1, 2].iter().cloned().collect(),
            "should exclude senders with 0 weight"
        );

        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, -1.0), (2, 1.0)].iter().cloned().collect(),
        );
        assert_eq!(
            SendersWeight::get_senders(&senders_weights),
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
            SendersWeight::get_senders(&senders_weights),
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
            SendersWeight::get_senders(&senders_weights),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with INFINITY weight"
        );
    }
}
