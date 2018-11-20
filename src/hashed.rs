use std::hash::{Hash, Hasher};
use std::fmt::{Debug, Formatter, Result as FmtResult};
use rayon::prelude::*;


/// structure for carrying hashed data
#[derive(Clone)]
pub struct Hashed([u8 ; 64]);

impl Hash for Hashed {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

// impl PartialOrd for Hashed {
//     fn partial_cmp(&self, rhs: &Self) -> Option<::std::cmp::Ordering>{
//         Some(self.cmp(rhs))
//     }
// }

// impl Ord for Hashed {
//     fn cmp(&self, rhs: &Self) -> ::std::cmp::Ordering {
//         let mut iter = Iterator::zip(self.0.iter(), rhs.0.iter());
//         loop {
//             if let Some((l, r)) = &iter.next() {
//                 if l > r { break ::std::cmp::Ordering::Greater }
//                 else if l < r { break ::std::cmp::Ordering::Less }
//             } else {
//                 // checked all bytes, and they were all equal
//                 { break ::std::cmp::Ordering::Equal }
//             };
//         }
//     }
// }

impl Eq for Hashed {}

impl PartialEq for Hashed{
    fn eq(&self, rhs: &Self) -> bool {
        self.0.par_iter().zip(rhs.0.par_iter())
            .all(|(l, r)| l == r)
    }
}

impl Default for Hashed {
    fn default() -> Self {
        Hashed([0u8 ; 64])
    }
}

impl Debug for Hashed {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        use itertools::Itertools;
        write!(
            f,
            "H{:?}",
            self.0.iter().format(""),
        )
    }
}

impl From<[u8 ; 64]> for Hashed {
    fn from(v: [u8 ; 64]) -> Self { Hashed(v) }
}

impl serde::Serialize for Hashed {
    fn serialize<T:serde::Serializer>(&self, serializer: T)-> Result<T::Ok, T::Error> {
        serializer.serialize_bytes(&self.0)
    }
}
