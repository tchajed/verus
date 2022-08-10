#![allow(unused_imports)]
/// Coke machine state machine exercise

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::{*, vec::Vec, option::*};
use crate::seq::Seq;

verus! {

  #[derive(PartialEq, Eq, Structural)]
  struct Constants { capacity: int }
  #[derive(PartialEq, Eq, Structural)]
  struct CokeMachine { num_cokes: int }

  impl CokeMachine {
    spec fn init(self, c: Constants) -> bool {
      &&& self.num_cokes == 0
      &&& c.capacity >= 0
    }

    spec fn purchase(self, c: Constants, next: Self) -> bool {
      // precondition
      &&& self.num_cokes > 0
      // transition
      &&& next == CokeMachine { num_cokes: self.num_cokes - 1 }
    }

    spec fn restock(self, c: Constants, next: Self, num_restock: int) -> bool {
      // precondition
      &&& self.num_cokes + num_restock <= c.capacity
      // transition
      &&& next == CokeMachine { num_cokes: self.num_cokes + num_restock }
    }

    spec fn next(self, c: Constants, next: Self) -> bool {
      ||| self.purchase(c, next)
      ||| exists |num: int| self.restock(c, next, num)
    }

    spec fn inv(&self, c: Constants) -> bool {
      &&& 0 <= self.num_cokes <= c.capacity
    }
  }

  proof fn safety_proof()
    ensures
      forall |c: Constants, v: CokeMachine| v.init(c) ==> v.inv(c),
      forall |c: Constants, v1: CokeMachine, v2: CokeMachine| v1.inv(c) ==> v1.next(c, v2) ==> v2.inv(c),
  {
  }

  fn main() {}

} // verus!
