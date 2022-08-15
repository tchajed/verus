#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::set::*;
use pervasive::set_lib::{lemma_len0_is_empty, lemma_len_subset};

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

  pub open spec fn map_fold<A, B, F: Fn(A) -> B>(s: Set<A>, f: F) -> Set<B> {
    s.right_fold::<Set<B>, _>(|x, ss| ss.insert(f(x)), Set::empty())
  }

  pub proof fn lemma_map_as_fold<A, B, F: Fn(A) -> B>(s: Set<A>, f: F)
    requires
      s.finite(),
    ensures
      s.map(f) === map_fold(s, f),
    decreases s.len(),
  {
    if s.len() == 0 {
      lemma_len0_is_empty::<A>(s);
      assert_sets_equal!(s.map(f), Set::empty());
    } else {
      let a = s.choose();
      lemma_map_as_fold::<A, B, F>(s.remove(a), f);

      assert(
        map_fold(s, f) ===
        map_fold(s.remove(a), f).insert(f(a))
      );
      assert(
        map_fold(s, f) === s.remove(a).map(f).insert(f(a))
      );

      let ms1 = map_fold(s, f);
      let ms2 = s.map(f);

      if s.remove(a).map(f).contains(f(a)) {
        assert(ms1.subset_of(ms2)); // obvious
        assert_forall_by(|b| {
          requires(s.map(f).contains(b));
          ensures(map_fold(s, f).contains(b));
          let a2 = choose |a2:A| s.contains(a2) && b === f(a2); // def of map
          if a !== a2 {
            assert(s.remove(a).contains(a2));
          }
        });
        assert(ms2.subset_of(ms1));
        assert_sets_equal!(ms1, ms2);
      } else {
        assert(ms1.subset_of(ms2)); // obvious
        assert_forall_by(|b| {
          requires(s.map(f).contains(b));
          ensures(map_fold(s, f).contains(b));
          let a2 = choose |a2:A| s.contains(a2) && b === f(a2); // def of map
          if a !== a2 {
            assert(s.remove(a).contains(a2));
          }
        });
        assert_sets_equal!(ms1, ms2);
      }
    }
  }

  pub proof fn lemma_len_map<A, B, F: Fn(A) -> B>(s: Set<A>, f: F)
      requires
          s.finite(),
      ensures
          s.map(f).finite(),
          s.map(f).len() <= s.len(),
      decreases
          s.len(),
  {
      lemma_map_as_fold::<A, B, F>(s, f);
      if s.len() == 0 {
        lemma_len0_is_empty::<A>(s);
        return;
      }

      let a = s.choose();
      lemma_len_map::<A, B, F>(s.remove(a), f);
      lemma_map_as_fold::<A, B, F>(s.remove(a), f);
  }

  fn main() {}
}
