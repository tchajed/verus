#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::{*, vec::Vec, option::*};
use crate::seq::Seq;
use std::ops::Index;

verus! {

  spec fn u64_le_bytes(x: u64) -> Seq<u8>;
  spec fn u64_from_le_bytes(s: Seq<u8>) -> u64;

  #[verifier(external_body)]
  proof fn axiom_u64_le_bytes(x: u64)
    ensures u64_le_bytes(x).len() == 8;

  #[verifier(external_body)]
  proof fn axiom_u64_from_le_bytes_ok(x: u64)
    ensures u64_from_le_bytes(u64_le_bytes(x)) === x;

  fn store_le_bytes(buf: &mut Vec<u8>, off: usize, x: u64)
    requires off + 8 <= old(buf).len()
    ensures buf@.subrange(off, off+8) === u64_le_bytes(x)
  {
    assume(false);
  }

  fn get_le_bytes(buf: &Vec<u8>, off: usize) -> (r:u64)
    requires off + 8 <= buf.len()
    ensures r === u64_from_le_bytes(buf@.subrange(off, off+8))
  {
    assume(false);
    0
  }

  struct Encoder {
    buf: Vec<u8>,
    off: usize,
  }

  impl Encoder {
    pub closed spec fn inv(self) -> bool {
      &&& self.off <= self.buf.len()
    }

    pub closed spec fn space(self) -> int {
      self.buf.len() - self.off
    }

    pub fn new(buf: Vec<u8>) -> (r:Self)
    ensures
      r.inv(),
      r.space() == buf.len(),
    {
      Encoder { buf: buf, off: 0 }
    }

    pub fn add_u8(&mut self, x: u8)
      requires
        old(self).inv(),
        old(self).space() > 1,
      ensures
        self.inv(),
        self.space() == old(self).space() - 1
     {
      let off = self.off;
      self.buf.set(off, x);
      self.off = off + 1;
     }
  }

  fn main() {}
}
