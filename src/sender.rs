use std::fmt::Debug;
use std::hash::Hash;

/// All casper actors that send messages have to implement the sender trait
pub trait Trait: Hash + Clone + Ord + Eq + Send + Sync + Debug + serde::Serialize {}

// Default implementations
impl Trait for u8 {}
impl Trait for u32 {}
impl Trait for u64 {}
impl Trait for i8 {}
impl Trait for i32 {}
impl Trait for i64 {}
