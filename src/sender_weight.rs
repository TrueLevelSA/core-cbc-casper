
use sender::Sender;
use weight_unit::WeightUnit;
use std::{f64};
use std::collections::{HashMap, HashSet};
use zero::{Zero};
use std::sync::{Arc};

pub struct SenderWeight<S: Sender>(Arc<HashMap<S, WeightUnit>>);

impl<S: Sender> SenderWeight<S> {
    /// picks senders with positive weights
    pub fn get_senders(
        senders_weights: &Arc<HashMap<S, WeightUnit>>,
    ) -> HashSet<S> {
        senders_weights
            .iter()
            .filter(|(_, &weight)| weight > WeightUnit::ZERO)
            .map(|(sender, _)| sender.clone())
            .collect()
    }

    pub fn get_weight(
        senders_weights: &Arc<HashMap<S, WeightUnit>>,
        sender: &S,
    ) -> WeightUnit {
        senders_weights.get(sender).unwrap_or(&f64::NAN).clone()
    }

    pub fn into_relative_weights(
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
mod sender_weight {
    use std::collections::{HashMap};
    use super::*;

    #[test]
    fn get_senders() {
        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            SenderWeight::get_senders(&senders_weights),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with valid, positive weight"
        );

        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 0.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            SenderWeight::get_senders(&senders_weights),
            [1, 2].iter().cloned().collect(),
            "should exclude senders with 0 weight"
        );

        let senders_weights: Arc<HashMap<u32, WeightUnit>> =
            Arc::new([(0, 1.0), (1, -1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            SenderWeight::get_senders(&senders_weights),
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
            SenderWeight::get_senders(&senders_weights),
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
            SenderWeight::get_senders(&senders_weights),
            [0, 1, 2].iter().cloned().collect(),
            "should include senders with INFINITY weight"
        );
    }
}
