use std::convert::From;

use message;
use message::CasperMsg;
use traits::{Data, Estimate};
use justification::Justification;
use senders_weight::SendersWeight;

type Validator = u32;

pub type Message = message::Message<Value, Validator>;

#[derive(Debug, Hash, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum Value {
    Zero = 0,
    One = 1,
}

impl Data for Value {
    type Data = Self;

    fn is_valid(_data: &Value) -> bool {
        true
    }
}

impl From<((Value, f64), (Value, f64))> for Value {
    fn from(val: ((Value, f64), (Value, f64))) -> Self {
        let ((v1, w1), (v2, w2)) = val;
        if w1 > w2 {
            v1
        } else {
            v2
        }
    }
}

impl Estimate for Value {
    type M = Message;

    fn mk_estimate(
        latest_msgs: &Justification<Message>,
        _finalized_msg: Option<&Message>,
        senders_weights: &SendersWeight<Validator>,
        _proto_block: Option<Value>,
    ) -> Value {
        latest_msgs.iter()
            .map(|msg| (msg.get_estimate(), senders_weights.get_weight(msg.get_sender())))
            .fold(((Value::Zero, 0f64), (Value::One, 0f64)), |acc, t| match t {
                (Value::Zero, Some(weight)) => (((acc.0).0, (acc.0).1 + weight), acc.1),
                (Value::One, Some(weight)) => (acc.0, ((acc.1).0, (acc.1).1 + weight)),
                _ => acc, // No weight for the given validator, do nothing
            }).into()
    }
}

#[test]
fn casper_binary_consensus() {
    use std::collections::HashSet;
    use justification::SenderState;

    let (sender1, sender2, sender3, sender4) = (1, 2, 3, 4);
    let (weight1, weight2, weight3, weight4) = (0.6, 1.0, 2.0, 1.3);

    let senders_weights = SendersWeight::new(
        [
            (sender1, weight1),
            (sender2, weight2),
            (sender3, weight3),
            (sender4, weight4),
        ].iter()
            .cloned()
            .collect(),
    );

    let weights = SenderState::new(
        senders_weights.clone(),
        0.0,            // state fault weight
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    // 1: (1)  (1)
    // 2: (1)       (0)
    // 3: (0)  (0)       (0)
    // 4: (1)  (0)

    let msg1 = Message::new(sender1, Justification::new(), Value::One);
    let msg2 = Message::new(sender2, Justification::new(), Value::One);
    let msg3 = Message::new(sender3, Justification::new(), Value::Zero);
    let msg4 = Message::new(sender4, Justification::new(), Value::One);
    let (msg5, _) = Message::from_msgs(sender1, vec![&msg1, &msg2], None, &weights, None).unwrap();
    let (msg6, _) = Message::from_msgs(sender3, vec![&msg3, &msg4], None, &weights, None).unwrap();
    let (msg7, _) = Message::from_msgs(sender2, vec![&msg2, &msg5, &msg6], None, &weights, None).unwrap();
    let (msg8, _) = Message::from_msgs(sender3, vec![&msg7, &msg6], None, &weights, None).unwrap();
    let (msg9, _) = Message::from_msgs(sender4, vec![&msg4, &msg6], None, &weights, None).unwrap();

    assert_eq!(msg5.get_estimate(), &Value::One);
    assert_eq!(msg6.get_estimate(), &Value::Zero);
    assert_eq!(msg7.get_estimate(), &Value::Zero);
    assert_eq!(msg8.get_estimate(), &Value::Zero);
    assert_eq!(msg9.get_estimate(), &Value::Zero);
}

