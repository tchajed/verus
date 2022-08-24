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
      &&& 0 <= num_restock
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
    assert_forall_by(|c, v1: CokeMachine, v2|
    {
      requires(v1.inv(c) && v1.next(c, v2));
      ensures(v2.inv(c));
      if v1.purchase(c, v2) {
      } else {
        let num = choose |num: int| v1.restock(c, v2, num);
      }
    })
  }

  proof fn non_trivial_purchase()
    ensures exists |c, v1: CokeMachine, v2| v1.inv(c) && v1.next(c, v2) && v2.num_cokes + 1 == v1.num_cokes
  {
    let c = Constants { capacity: 7 };
    let v1 = CokeMachine { num_cokes: 1 };
    let v2 = CokeMachine { num_cokes: 0 };
    assert(v1.inv(c) && v1.next(c, v2) && v2.num_cokes + 1 == v1.num_cokes);
  }

  proof fn non_trivial_restock()
    ensures exists |c, v1: CokeMachine, v2| v1.inv(c) && v1.next(c, v2) && v1.num_cokes < v2.num_cokes
  {
    let c = Constants { capacity: 7 };
    let v1 = CokeMachine { num_cokes: 4 };
    let v2 = CokeMachine { num_cokes: 7 };
    assert(v1.restock(c, v2, 3));
    assert(v1.inv(c) && v1.next(c, v2) && v1.num_cokes < v2.num_cokes);
  }

  fn main() {}

} // verus!
