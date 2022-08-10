#![allow(unused_imports)]
use builtin_macros::{verus};
use builtin::*;
mod pervasive;
use pervasive::{*, vec::Vec, option::*};
use crate::seq::Seq;

verus! {
  fn binary_search(v: &Vec<u64>) -> (r:Option<usize>)
    ensures
      match r {
        Option::Some(i) => true,
        Option::None => forall |i: int| v@[i] == 3u64,
      }
  {
    if false {
      return Option::Some(0);
    }
    Option::None
  }

  fn main() {}
} // verus!
