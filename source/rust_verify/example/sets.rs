#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::set::*;

verus! {
  pub open spec fn set_fold<T, R, F: Fn(T, R) -> R>(s: Set<T>, f: F, zero: R, count: nat) -> R {
      decreases(count);
      if count == 0 {
          zero
      } else {
          let x = s.choose();
          f(x, set_fold(s.remove(x), f, zero, (count-1) as nat))
      }
  }

  pub open spec fn max(n: nat, m: nat) -> nat {
    if n > m { n } else { m }
  }

  pub open spec fn set_max(s: Set<nat>) -> (m: nat)
  {
    set_fold(s, |x, y| max(x, y), 0, s.len())
  }

  pub proof fn set_max_fold_ok(s: Set<nat>, count: nat)
    requires
      s.finite(),
      count == s.len(),
    ensures forall |n: nat| s.contains(n) ==> set_fold(s, |x, y| max(x, y), 0, count) >= n
  {
    decreases(count);
    if s.len() == 0 {
      assume(s === Set::empty());
    } else {
      let x = s.choose();
      set_max_fold_ok(s.remove(x), (count-1) as nat);
      assert_forall_by(|n: nat| {
        requires(s.contains(n));
        ensures(set_fold(s, |x, y| max(x, y), 0, count) >= n);
        if x != n {
          assert(s.remove(x).contains(n));
        } else {
        }
      })
    }
  }

  pub proof fn set_max_ok(s: Set<nat>)
    requires s.finite()
    ensures forall |n: nat| s.contains(n) ==> set_max(s) >= n
  {
    set_max_fold_ok(s, s.len());
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
