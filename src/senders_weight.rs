use std::collections::{HashMap, HashSet};
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard, LockResult};

use weight_unit::WeightUnit;
use traits::{Zero, Sender};

// RwLock locks only before writing, while Mutex locks to both read and write

#[derive(Clone, Default, Debug)]
pub struct SendersWeight<S: Sender>(Arc<RwLock<HashMap<S, WeightUnit>>>);

impl<S: Sender> SendersWeight<S> {
    pub fn new(senders_weight: HashMap<S, WeightUnit>) -> Self {
        SendersWeight(Arc::new(RwLock::new(senders_weight)))
    }

    pub fn read(&self) -> LockResult<RwLockReadGuard<HashMap<S, WeightUnit>>> {
        self.0.read()
    }

    pub fn write(
        &self,
    ) -> LockResult<RwLockWriteGuard<HashMap<S, WeightUnit>>> {
        self.0.write()
    }

    /// picks senders with positive weights
    pub fn get_senders(&self) -> Result<HashSet<S>, &'static str> {
        self.read().map_err(|_| "Can't unwrap SendersWeight").map(
            |senders_weight| {
                senders_weight
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
            },
        )
    }

    pub fn get_weight(&self, sender: &S) -> Result<WeightUnit, &'static str> {
        self.read()
            .map_err(|_| "Can't unwrap SendersWeight")
            .and_then(|weights| match weights.get(sender) {
                Some(weight) => Ok(weight.clone()),
                None => Err("Could not find sender"),
            })
    }

    pub fn sum_weight_senders(&self, senders: &HashSet<S>) -> WeightUnit {
        senders.iter().fold(WeightUnit::ZERO, |acc, sender| {
            acc + self.get_weight(sender).unwrap_or(::std::f64::NAN)
        })
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
            SendersWeight::get_senders(&senders_weights).unwrap(),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with valid, positive weight"
        );

        let senders_weights = SendersWeight::new(
            [(0, 0.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        );
        assert_eq!(
            SendersWeight::get_senders(&senders_weights).unwrap(),
            [1, 2].iter().cloned().collect(),
            "should exclude senders with 0 weight"
        );

        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, -1.0), (2, 1.0)].iter().cloned().collect(),
        );
        assert_eq!(
            SendersWeight::get_senders(&senders_weights).unwrap(),
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
            SendersWeight::get_senders(&senders_weights).unwrap(),
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
            SendersWeight::get_senders(&senders_weights).unwrap(),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with INFINITY weight"
        );
    }
}
