use sender::Sender;
use weight_unit::WeightUnit;
use std::collections::{HashMap, HashSet};
use zero::{Zero};
use std::sync::{Arc, RwLock, PoisonError, RwLockReadGuard, RwLockWriteGuard};

// RwLock locks only before writing, while Mutex locks to both read and write
#[derive(Clone, Default, Debug)]
pub struct SendersWeight<S: Sender>(Arc<RwLock<HashMap<S, WeightUnit>>>);

impl<S: Sender> SendersWeight<S> {
    pub fn new(senders_weight: HashMap<S, WeightUnit>) -> Self {
        SendersWeight(Arc::new(RwLock::new(senders_weight)))
    }
    fn read(
        &self,
    ) -> Result<
        RwLockReadGuard<HashMap<S, WeightUnit>>,
        PoisonError<RwLockReadGuard<HashMap<S, WeightUnit>>>,
    > {
        self.0.read()
    }

    fn write(
        &self,
    ) -> Result<
        RwLockWriteGuard<HashMap<S, WeightUnit>>,
        PoisonError<RwLockWriteGuard<HashMap<S, WeightUnit>>>,
    > {
        self.0.write()
    }
    /// picks senders with positive weights
    pub fn get_senders(senders_weights: &Self) -> HashSet<S> {
        senders_weights
            .read()
            .unwrap()
            .iter()
            .filter(|(_, &weight)| weight > WeightUnit::ZERO)
            .map(|(sender, _)| sender.clone())
            .collect()
    }

    pub fn get_weight(
        senders_weights: &Self,
        sender: &S,
        base_value: WeightUnit,
    ) -> WeightUnit {
        senders_weights
            .read()
            .unwrap()
            .get(sender)
            .unwrap_or(&base_value)
            .clone()
    }

    pub fn into_relative_weights(senders_weights: &Self) -> Self {
        let senders_weights = senders_weights.read().unwrap();

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
