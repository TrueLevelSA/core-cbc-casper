
use sender::Sender;
use weight_unit::WeightUnit;
use std::collections::{HashMap, HashSet};
use zero::{Zero};
use std::sync::{Arc, RwLock};

type SenderW<S> = Arc<RwLock<HashMap<S, WeightUnit>>>; // FIXME: remove this after
                                                       // after SenderWeight is fully implemented

// RwLock locks only before writing, while Mutex locks to both read and write
pub struct SenderWeight<S: Sender>(Arc<RwLock<HashMap<S, WeightUnit>>>);

impl<S: Sender> SenderWeight<S> {
    /// picks senders with positive weights
    pub fn get_senders(senders_weights: SenderW<S>) -> HashSet<S> {
        senders_weights
            .read()
            .unwrap()
            .iter()
            .filter(|(_, &weight)| weight > WeightUnit::ZERO)
            .map(|(sender, _)| sender.clone())
            .collect()
    }

    pub fn get_weight(senders_weights: SenderW<S>, sender: &S, base_value: WeightUnit) -> WeightUnit {
        senders_weights
            .read()
            .unwrap()
            .get(sender)
            .unwrap_or(&base_value)
            .clone()
    }

    pub fn into_relative_weights(senders_weights: SenderW<S>) -> SenderW<S> {
        let senders_weights = senders_weights
            .read()
            .unwrap();

        let iterator = senders_weights
            .iter()
            .filter(|(_, &weight)| weight > WeightUnit::ZERO);

        let total_weight: WeightUnit = iterator
            .clone()
            .fold(WeightUnit::ZERO, |acc, (_, weight)| acc + weight);

        Arc::new(RwLock::new(
            iterator
                .map(|(sender, weight)| {
                    (sender.clone(), weight.clone() / total_weight)
                })
                .collect(),
        ))
    }
}

#[cfg(test)]
mod sender_weight {
    use super::*;

    #[test]
    fn get_senders() {
        let senders_weights = Arc::new(RwLock::new(
            [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        ));
        assert_eq!(
            SenderWeight::get_senders(senders_weights.clone()),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with valid, positive weight"
        );

        let senders_weights = Arc::new(RwLock::new(
            [(0, 0.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        ));
        assert_eq!(
            SenderWeight::get_senders(senders_weights.clone()),
            [1, 2].iter().cloned().collect(),
            "should exclude senders with 0 weight"
        );

        let senders_weights =
            Arc::new(RwLock::new([(0, 1.0), (1, -1.0), (2, 1.0)].iter().cloned().collect()));
        assert_eq!(
            SenderWeight::get_senders(senders_weights.clone()),
            [0, 2].iter().cloned().collect(),
            "should exclude senders with negative weight"
        );

        let senders_weights = Arc::new(RwLock::new(
            [(0, ::std::f64::NAN), (1, 1.0), (2, 1.0)]
                .iter()
                .cloned()
                .collect(),
        ));
        assert_eq!(
            SenderWeight::get_senders(senders_weights.clone()),
            [1, 2].iter().cloned().collect(),
            "should exclude senders with NAN weight"
        );

        let senders_weights = Arc::new(RwLock::new(
            [(0, ::std::f64::INFINITY), (1, 1.0), (2, 1.0)]
                .iter()
                .cloned()
                .collect(),
        ));
        assert_eq!(
            SenderWeight::get_senders(senders_weights.clone()),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with INFINITY weight"
        );
    }
}
