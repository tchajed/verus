#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::set::*;
use pervasive::set_lib::lemma_len0_is_empty;

verus! {
  impl<A> Set<A> {
    pub open spec fn right_fold<R, F: Fn(A, R) -> R>(self, f: F, init: R) -> R
      decreases self.len()
    {
      if self.finite() {
        if self.len() == 0 {
            init
        } else {
            let x = self.choose();
            f(x, self.remove(x).right_fold(f, init))
        }
      } else {
        init
      }
    }
  }

  pub open spec fn set_max(s: Set<nat>) -> (m: nat)
  {
    s.right_fold(|x, y| if x > y { x } else { y }, 0)
  }

  pub proof fn set_max_ok(s: Set<nat>)
    requires
      s.finite(),
    ensures forall |n: nat| s.contains(n) ==> set_max(s) >= n,
    decreases s.len(),
  {
    if s.len() == 0 {
      lemma_len0_is_empty::<nat>(s);
    } else {
      let x = s.choose();
      set_max_ok(s.remove(x));
      assert_forall_by(|n: nat| {
        requires(s.contains(n));
        ensures(set_max(s) >= n);
        if x != n {
          assert(s.remove(x).contains(n));
        } else {
        }
      })
    }
  }

  pub closed spec fn get_new_nat(s: Set<nat>) -> nat
  {
    set_max(s) + 1
  }

  pub proof fn get_new_nat_not_in(s: Set<nat>)
    requires s.finite()
    ensures !s.contains(get_new_nat(s))
  {
    set_max_ok(s);
  }

  fn main() {}
}
