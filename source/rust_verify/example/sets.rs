#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::set::*;

verus! {
  pub open spec fn set_fold<T, R, F: Fn(R, T) -> R>(s: Set<T>, f: F, acc: R, count: nat) -> R {
      decreases(count);
      if count == 0 {
          acc
      } else {
          let x = s.choose();
          set_fold(s.remove(x), f, f(acc, x), (count-1) as nat)
      }
  }

  pub open spec fn max(n: nat, m: nat) -> nat {
    if n > m { n } else { m }
  }

  pub open spec fn set_max(s: Set<nat>) -> (m: nat)
  {
    set_fold(s, |n, m| max(n, m), 0, s.len())
  }

  pub proof fn set_max_ok(s: Set<nat>)
    requires s.finite()
    ensures forall |n: nat| s.contains(n) ==> set_max(s) >= n
  {
    decreases(s.len());
    if s.len() == 0 {
      assume(s === Set::empty());
      assert(forall |n: nat| !s.contains(n));
    } else {
      let x = s.choose();
      set_max_ok(s.remove(x));
      assert_forall_by(|n: nat| {
        requires(s.contains(n));
        ensures(set_max(s) >= n);
        if x != n {
          assert(s.remove(x).contains(n));
          assert(set_max(s.remove(x)) >= n);
          assert(set_max(s) === max(set_max(s.remove(x)), x));
        } else {
          assume(false);
        }
      })
    }
  }

  fn main() {}
}
