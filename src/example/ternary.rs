use std::convert::From;

use message;
use traits::{Data, Estimate};
use justification::LatestMsgsHonest;
use senders_weight::SendersWeight;

type Validator = u32;

pub type Message = message::Message<Value, Validator>;

#[derive(Debug, Hash, Clone, Copy, Ord, PartialOrd, Eq, PartialEq)]
pub enum Value {
    Zero = 0,
    One = 1,
    Two = 2,
}

impl Data for Value {
    type Data = Self;

    fn is_valid(_data: &Value) -> bool {
        true
    }
}

impl From<((Value, f64), (Value, f64), (Value, f64))> for Value {
    /// If equality between two or tree values exists, last value is
    /// prefered, then second value, and first value
    ///
    /// v1: w1 > w2,  w1 > w3
    /// v2: w2 >= w1, w2 > w3
    /// v3: w3 >= w1, w3 >= w1
    ///
    fn from(val: ((Value, f64), (Value, f64), (Value, f64))) -> Self {
        let ((v1, w1), (v2, w2), (v3, w3)) = val;
        let mut max = v3;
        let mut w = w3;
        if w2 > w {
            max = v2;
            w = w2;
        }
        if w1 > w {
            max = v1;
        }
        max
    }
}

impl Estimate for Value {
    type M = Message;

    fn mk_estimate(
        latest_msgs: &LatestMsgsHonest<Message>,
        _finalized_msg: Option<&Message>,
        senders_weights: &SendersWeight<Validator>,
        _proto_block: Option<Value>,
    ) -> Value {
        use message::CasperMsg;
        latest_msgs.iter()
            .map(|msg| (msg.get_estimate(), senders_weights.get_weight(msg.get_sender())))
            .fold(((Value::Zero, 0f64), (Value::One, 0f64), (Value::Two, 0f64)), |acc, t| match t {
                (Value::Zero, Ok(weight)) => (((acc.0).0, (acc.0).1 + weight), acc.1, acc.2),
                (Value::One, Ok(weight)) => (acc.0, ((acc.1).0, (acc.1).1 + weight), acc.2),
                (Value::Two, Ok(weight)) => (acc.0, acc.1, ((acc.2).0, (acc.2).1 + weight)),
                _ => acc, // No weight for the given validator, do nothing
            }).into()
    }
}

#[test]
fn casper_binary_consensus() {
    use message::CasperMsg;
    use std::collections::HashSet;
    use justification::{SenderState, Justification, LatestMsgs};

    let senders: Vec<u32> = (1..=4).collect();
    let weights = [0.6, 1.0, 2.0, 1.3];

    let senders_weights = SendersWeight::new(
        senders
            .iter()
            .cloned()
            .zip(weights.iter().cloned())
            .collect(),
    );

    let weights = SenderState::new(
        senders_weights.clone(),
        0.0, // state fault weight
        None,
        LatestMsgs::new(),
        1.0,            // subjective fault weight threshold
        HashSet::new(), // equivocators
    );

    // 1: (1)  (2)
    // 2: (2)       (0)
    // 3: (0)  (0)       (0)
    // 4: (1)  (0)

    let msg1 = Message::new(1, Justification::new(), Value::One);
    let msg2 = Message::new(2, Justification::new(), Value::Two);
    let msg3 = Message::new(3, Justification::new(), Value::Zero);
    let msg4 = Message::new(4, Justification::new(), Value::One);
    let (msg5, _) = Message::from_msgs(1, vec![&msg1, &msg2], None, &weights, None).unwrap();
    let (msg6, _) = Message::from_msgs(3, vec![&msg3, &msg4], None, &weights, None).unwrap();
    let (msg7, _) = Message::from_msgs(2, vec![&msg2, &msg5, &msg6], None, &weights, None).unwrap();
    let (msg8, _) = Message::from_msgs(3, vec![&msg7, &msg6], None, &weights, None).unwrap();
    let (msg9, _) = Message::from_msgs(4, vec![&msg4, &msg6], None, &weights, None).unwrap();

    assert_eq!(msg5.get_estimate(), &Value::Two);
    assert_eq!(msg6.get_estimate(), &Value::Zero);
    assert_eq!(msg7.get_estimate(), &Value::Zero);
    assert_eq!(msg8.get_estimate(), &Value::Zero);
    assert_eq!(msg9.get_estimate(), &Value::Zero);
}
