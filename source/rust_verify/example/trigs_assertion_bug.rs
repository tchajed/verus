#![allow(unused_imports)]
use builtin_macros::verus;
use builtin::int;
mod pervasive;
use pervasive::vec::Vec;

verus! {
  fn binary_search(v: &Vec<bool>)
    ensures forall |i: int| v@[i],
  {
    if false {
      return;
    }
  }

  fn main() {}
} // verus!
