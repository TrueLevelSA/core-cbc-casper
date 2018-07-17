use std::hash::{Hash};
use std::fmt::{Debug};

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}
