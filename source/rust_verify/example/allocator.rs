#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::{*, ptr::*, map::*, vec::*};

verus! {
  struct Allocator<V> {
    block: Vec<PPtr<V>>,
    perms: Tracked<Map<nat, PermissionOpt<V>>>,
  }

  impl<V> Allocator<V> {
    fn new(size: usize) -> Self {
      let mut block = Vec::new();
      let mut perms = tracked(Map::tracked_empty());
      let mut i = 0;
      while i < size {
        let (p, perm) = PPtr::empty();
        block.push(p);
        proof {
          // what a mess! can't even let-bind perms.borrow_mut(), results in an
          // error
          (tracked perms.borrow_mut())
            .tracked_insert(i as nat, (tracked perm).get());
        }
        i = i + 1;
      }
      Allocator { block, perms }
    }
  }

  fn main() {}
}
