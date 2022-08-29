#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::{*, ptr::*, map::*, vec::*, set::*, option::*};
use pervasive::option::Option::*;

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
    // the next index into block to give out
    next: usize,
  }

  impl<V> Allocator<V> {
    closed spec fn wf_perm_ids(self) -> bool {
      forall |i: int| #[auto_trigger] self.next <= i < self.block@.len() ==>
            self.block@[i].id() == self.perms@[i as nat]@.pptr && self.block@[i].id() != 0
    }

    closed spec fn wf(self) -> bool {
      &&& self.perms@.dom() === Set::new(|n: nat| self.next <= n < self.block@.len())
      &&& self.perms@.dom().finite()
      &&& self.wf_perm_ids()
    }

    fn new(size: usize) -> (v:Self)
      ensures v.wf()
    {
      let mut block: Vec<PPtr<V>> = Vec::new();
      let mut perms = tracked(Map::tracked_empty());
      proof {
        assert(perms@.dom() === Set::empty());
        assert_sets_equal!(Set::new(|n: nat| 0 <= n && n < 0), Set::empty());
      }
      let mut i: usize = 0;
      while i < size
      {
        invariant([
          block@.len() == i,
          Allocator { block, perms, next: 0 }.wf(),
        ]);
        let (p, perm) = PPtr::empty();
        block.push(p);

        proof {
          // what a mess! everything has to be marked tracked
          let tracked perm = (tracked perm).get();
          (tracked &perm).is_nonnull();
          (tracked perms.borrow_mut())
            .tracked_insert(i as nat, tracked perm);
          assert_sets_equal!(
            perms.view().dom(),
            Set::new(|n: nat| 0 <= n && n < i+1 as nat));
        }

        i = i + 1;
      }
      Allocator { block, perms, next: 0 }
    }

    fn alloc(&mut self) -> (rv: Option<(&PPtr<V>, Tracked<PermissionOpt<V>>)>)
    requires old(self).wf()
    ensures
      rv.is_Some() ==> rv.get_Some_0().0.id() == rv.get_Some_0().1@@.pptr,
      self.wf(),
      self.block@.len() == old(self).block@.len()
    {
      let next = self.next;
      if next >= self.block.len() {
        // out of space
        return None;
      }
      let p = self.block.index(next);
      self.next = next + 1;
      let perm: Tracked<PermissionOpt<V>> = tracked((tracked self.perms.borrow_mut()).tracked_remove(next));
      assert(perm@@.pptr === p.id());
      proof {
        assert_sets_equal!(
        self.perms.view().dom(),
        Set::new(|n: nat| (next + 1) as nat <= n && n < self.block.view().len()));
        assert(self.wf_perm_ids());
      }
      return Some((p, perm));
    }
  }

  fn main() {}
}
