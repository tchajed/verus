#![allow(unused_imports)]
use builtin_macros::{verus};
use builtin::*;
mod pervasive;
use pervasive::{*, vec::Vec, option::*};
use crate::seq::Seq;

verus! {
  spec fn is_sorted(v: Seq<u64>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j]
  }

  /// Search for needle in a sorted vector `v`.
  ///
  /// Returns None if needle is not present
  fn binary_search(v: &Vec<u64>, needle: u64) -> (r:Option<usize>)
    requires
      is_sorted(v@),
    ensures
      match r {
        Option::Some(i) => 0 <= i < v.len() && v@[i] == needle,
        Option::None => forall |i: int|
          0 <= i < v.len() ==> v@[i] != needle,
      }
  {
    let mut start: usize = 0;
    let mut end: usize = v.len();

    while end > start
      invariant
        start <= end <= v.len(),
        is_sorted(v@),
        // forall |i: int| #[trigger] !(start <= i < end) ==> v@[i] != needle,
    {
      let mid = start + (end - start) / 2;
      let x = *v.index(mid);
      if needle == x {
        return Option::Some(mid);
      }
      if needle < x {
        end = mid + 1;
      } else {
        start = mid;
      }
    }
    Option::None
  }

  fn main() {}
} // verus!
