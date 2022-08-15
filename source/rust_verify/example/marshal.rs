#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
mod pervasive;
use crate::seq::Seq;
use pervasive::{option::*, vec::Vec, *};
use std::ops::Index;

mod enc {
    use super::pervasive::{vec::*, *};
    use crate::seq::Seq;
    use builtin::*;
    use builtin_macros::*;

    use std::convert::TryInto;

    verus! {
      pub closed spec fn u64_le_bytes(x: u64) -> Seq<u8>;
      pub closed spec fn u64_from_le_bytes(s: Seq<u8>) -> u64;

      #[verifier(external_body)]
      pub proof fn axiom_u64_le_bytes(x: u64)
        ensures u64_le_bytes(x).len() == 8;

      #[verifier(external_body)]
      pub proof fn axiom_u64_from_le_bytes_ok(x: u64)
        ensures u64_from_le_bytes(u64_le_bytes(x)) === x;

      #[verifier(external_body)]
      pub fn store_le_bytes(buf: &mut Vec<u8>, off: usize, x: u64)
        requires off + 8 <= old(buf).len()
        ensures buf@ === old(buf)@.subrange(0, off).add(
          u64_le_bytes(x)
        ).add(old(buf)@.subrange(off+8, old(buf)@.len()))
      {
        buf.vec[off..off+8].copy_from_slice(&x.to_le_bytes());
      }

      fn test_store_le_bytes(buf: &mut Vec<u8>, off: usize, x: u64)
        requires off + 8 <= old(buf).len()
      {
        proof { let data = buf@; }
        store_le_bytes(buf, off, x);
        proof {
          axiom_u64_le_bytes(x);
          assert( buf@.len() === old(buf)@.len() );
        }
      }

      #[verifier(external_body)]
      pub fn get_le_bytes(buf: &Vec<u8>, off: usize) -> (r:u64)
        requires off + 8 <= buf.len()
        ensures r === u64_from_le_bytes(buf@.subrange(off, off+8))
      {
        u64::from_le_bytes(buf.vec[off..off+8].try_into().unwrap())
      }

    }
}

verus! {
  use enc::*;

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

    pub closed spec fn view(self) -> Seq<u8>
      recommends self.inv()
    {
      self.buf@.subrange(0, self.off)
    }

    pub fn new(buf: Vec<u8>) -> (r:Self)
    ensures
      r.inv(),
      r.space() == buf.len(),
      r@ === seq![],
    {
      let r = Encoder { buf: buf, off: 0 };
      proof { assert_seqs_equal!(r.view(), seq![]); }
      r
    }

    pub fn add_u8(&mut self, x: u8)
      requires
        old(self).inv(),
        old(self).space() >= 1,
      ensures
        self.inv(),
        self.space() == old(self).space() - 1,
        self@ === old(self)@.push(x),
     {
      let off = self.off;
      self.buf.set(off, x);
      self.off = off + 1;
      proof { assert_seqs_equal!(self.view(), old(self).view().push(x)); }
     }

     pub fn add_u64(&mut self, x: u64)
       requires
         old(self).inv(),
         old(self).space() >= 8,
        ensures
          self.inv(),
          self.space() == old(self).space() - 8,
          self@ === old(self)@.add(u64_le_bytes(x)),
      {
        let off = self.off;
        store_le_bytes(&mut self.buf, off, x);
        self.off = off + 8;
        proof {
          axiom_u64_le_bytes(x);
          assert_seqs_equal!(self.view(), old(self).view().add(u64_le_bytes(x)));
        }
      }
  }

  fn main() {}
}
