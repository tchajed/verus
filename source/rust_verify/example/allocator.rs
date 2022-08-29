#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::{*, ptr::*, map::*, vec::*, set::*};

verus! {
  pub proof fn set_insert_contains<V>(s: Set<V>, a: V)
    ensures forall |x: V| s.contains(x) == s.contains(x) || x === a
  {
    assert_forall_by(|x: V| {
      ensures(s.contains(x) == s.contains(x) || x === a);
      if x === a {}
    })
  }

  struct Allocator<V> {
    block: Vec<PPtr<V>>,
    perms: Tracked<Map<nat, PermissionOpt<V>>>,
  }

  impl<V> Allocator<V> {
    closed spec fn wf(self) -> bool {
      &&& self.perms@.dom() === Set::new(|n: nat| n < self.block.len())
      &&& self.perms@.dom().finite()
    }

    fn new(size: usize) -> (v:Self)
      ensures v.wf()
    {
      let mut block: Vec<PPtr<V>> = Vec::new();
      let mut perms = tracked(Map::tracked_empty());
      proof {
        assert(perms@.dom() === Set::empty());
        assert_sets_equal!(Set::new(|n: nat| n < 0), Set::empty());
      }
      let mut i: usize = 0;
      while i < size
      {
        invariant([
          block.len() == i,
          perms@.dom() === Set::new(|n: nat| n < i),
          Allocator { block, perms }.wf(),
        ]);
        let (p, perm) = PPtr::empty();
        block.push(p);

        proof {
          // what a mess! can't even let-bind perms.borrow_mut(), results in an
          // error
          (tracked perms.borrow_mut())
            .tracked_insert(i as nat, (tracked perm).get());
          assert_sets_equal!(perms.view().dom(), Set::new(|n: nat| n < i+1 as nat));
        }

        i = i + 1;
      }
      Allocator { block, perms }
    }
  }

  fn main() {}
}
