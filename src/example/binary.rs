use traits::{Estimate, Data, Zero};
use message::{CasperMsg, Message};
use justification::{LatestMsgs};
use senders_weight::{SendersWeight};
use weight_unit::{WeightUnit};
type Validator = u32;

pub type BinaryMsg = Message<bool /*Estimate*/, Validator /*Sender*/>;

impl Data for bool {
    type Data = Self;
    fn is_valid(_data: &Self::Data) -> bool {
        true // FIXME
    }
}
impl Estimate for bool {
    type M = BinaryMsg;
    fn mk_estimate(
        latest_msgs: &LatestMsgs<Self::M>,
        _finalized_msg: Option<&Self::M>,
        senders_weights: &SendersWeight<
            <<Self as Estimate>::M as CasperMsg>::Sender,
        >,
        _data: Option<<Self as Data>::Data>,
    ) -> Self {
        let (true_w, false_w) = latest_msgs.iter().fold(
            (WeightUnit::ZERO, WeightUnit::ZERO),
            |(true_w, false_w), (sender_current, msgs)| {
                let (true_w_intermediate, false_w_intermediate) =
                    msgs.iter().fold(
                        (WeightUnit::ZERO, WeightUnit::ZERO),
                        |(true_w, false_w), msg| {
                            let sender_weight = senders_weights
                                .get_weight(sender_current)
                                .unwrap_or(WeightUnit::ZERO);
                            if *msg.get_estimate() {
                                (true_w + sender_weight, false_w)
                            } else {
                                (true_w, false_w + sender_weight)
                            }
                        },
                    );
                (true_w + true_w_intermediate, false_w + false_w_intermediate)
            },
        );
        true_w >= false_w
    }
}
