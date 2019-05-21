use casper::justification::LatestMsgsHonest;
use casper::message::{self, Trait};
use casper::traits::{Estimate, Zero};
use casper::util::weight::{SendersWeight, WeightUnit};

type Validator = u32;

#[derive(Clone, Eq, PartialEq, Debug, Hash, serde_derive::Serialize)]
pub struct BoolWrapper(pub bool);

impl BoolWrapper {
    pub fn new(estimate: bool) -> Self {
        BoolWrapper(estimate)
    }
}

#[cfg(feature = "integration_test")]
impl<S: casper::traits::Sender> From<S> for BoolWrapper {
    fn from(_sender: S) -> Self {
        BoolWrapper::new(bool::default())
    }
}

pub type BinaryMsg = message::Message<BoolWrapper /*Estimate*/, Validator /*Sender*/>;

impl Estimate for BoolWrapper {
    type M = BinaryMsg;

    /// weighted count of the votes contained in the latest messages
    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Self::M>,
        senders_weights: &SendersWeight<<<Self as Estimate>::M as message::Trait>::Sender>,
        // _data: Option<<Self as Data>::Data>,
    ) -> Result<Self, &'static str> {
        // loop over all the latest messages
        let (true_w, false_w) = latest_msgs.iter().fold(
            (WeightUnit::ZERO, WeightUnit::ZERO),
            |(true_w, false_w), msg| {
                // get the weight for the sender
                let sender_weight = senders_weights
                    .weight(msg.sender())
                    .unwrap_or(WeightUnit::ZERO);

                // add the weight to the right accumulator
                if msg.estimate().0.clone() {
                    (true_w + sender_weight, false_w)
                } else {
                    (true_w, false_w + sender_weight)
                }
            },
        );

        Ok(BoolWrapper(true_w >= false_w))
    }
}
