#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;

verus! {
  proof fn it_works()
    ensures true
  {}

  fn main() {}
}
