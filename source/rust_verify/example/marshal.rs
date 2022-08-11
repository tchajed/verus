#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::{*, vec::Vec, option::*};
use crate::seq::Seq;
use std::ops::Index;

verus! {

  // TODO: how do I put requires/ensures on these spec functions? (these should
  // only be length-8 sequences)
  spec fn u64_le_bytes(x: u64) -> Seq<u8>;
  spec fn u64_from_le_bytes(b: Seq<u8>) -> u64;

  // TODO: how to get the model of a slice?
  spec fn slice_seq(r: &[u8]) -> Seq<u8>;

  fn to_le_bytes64(x: u64) -> (r:[u8; 8])
    ensures slice_seq(r.index(..)) === u64_le_bytes(x)
  {
    assume(false);
    proof_from_false()
  }

  fn from_le_bytes64(bs: &[u8]) -> (r:u64)
    requires bs.len() == 8
    ensures r == u64_from_le_bytes(slice_seq(bs))
  {
    assume(false);
    proof_from_false()
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
