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
  /// Requires that needle is actually present in the vector.
  fn binary_search_present(v: &Vec<u64>, needle: u64) -> usize
    requires
      is_sorted(v@),
      exists |i: int| 0 <= i < v.len() && v@[i] == needle,
  {
    let mut start: usize = 0;
    let mut end: usize = v.len();

    proof {
      let goal: int = choose |i: int| 0 <= i < v.len() && v[i] == needle;
    }

    while end > start
      invariant
        start <= end <= v.len(),
        is_sorted(v@),
        exists |i: int| start <= i < end && v@[i] == needle,
    {
      let mid = start + (end - start) / 2;
      let x = *v.index(mid);
      if needle < x {
        end = mid + 1;
      } else {
        start = mid;
      }
    }
    assert (start == end);
    start
  }


  fn main() {}
} // verus!
