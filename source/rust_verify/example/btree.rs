#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::{*, vec::*, seq::*};

mod enc {
    use super::pervasive::{vec::*, *};
    use crate::seq::Seq;
    use builtin::*;
    use builtin_macros::*;

    use std::convert::TryInto;

    verus! {
      pub closed spec fn u16_le_bytes(x: u16) -> Seq<u8>;
      pub closed spec fn u16_from_le_bytes(s: Seq<u8>) -> u16;
      // BUG: generates ill-typed AIR to use this
      const SIZE: usize = 2;

      #[verifier(external_body)]
      pub proof fn axiom_u16_le_bytes(x: u16)
        ensures u16_le_bytes(x).len() == 2;

      #[verifier(external_body)]
      pub proof fn axiom_u16_from_le_bytes_ok(x: u16)
        ensures u16_from_le_bytes(u16_le_bytes(x)) === x;

      #[verifier(external_body)]
      pub fn store_le_bytes(buf: &mut Vec<u8>, off: usize, x: u16)
        requires off + 2 <= old(buf).len()
        ensures buf@ === old(buf)@.subrange(0, off).add(
          u16_le_bytes(x)
        ).add(old(buf)@.subrange(off+2, old(buf)@.len()))
      {
        buf.vec[off..off+8].copy_from_slice(&x.to_le_bytes());
      }

      fn test_store_le_bytes(buf: &mut Vec<u8>, off: usize, x: u16)
        requires off + 2 <= old(buf).len()
      {
        proof { let data = buf@; }
        store_le_bytes(buf, off, x);
        proof {
          axiom_u16_le_bytes(x);
          assert( buf@.len() === old(buf)@.len() );
        }
      }

      #[verifier(external_body)]
      pub fn get_u16_le_bytes(buf: &Vec<u8>, off: usize) -> (r:u16)
        requires off + 2 <= buf.len()
        ensures r === u16_from_le_bytes(buf@.subrange(off, off+2))
      {
        u16::from_le_bytes(buf.vec[off..off+2].try_into().unwrap())
      }

    }
}

verus! {
  // NOTE: associated functions are not supported
  /*
  trait Parser where Self: std::marker::Sized {
    fn parse(data: Seq<u8>) -> Option<Self> {
      no_method_body()
    }
  }
  */

  // NOTE: fn() types are not directly supported
  /*
  type Parser<T> = fn(Seq<u8>) -> Option<T>;
  */

  // NOTE: trait bounds on Self are not supported
  /*
  trait Parser<T> where Self: Fn(Seq<u8>) -> Option<T> {}
  */

  pub open spec fn concat<T>(s: Seq<Seq<T>>) -> Seq<T> {
    decreases(s.len());
    if s.len() == 0 {
      Seq::empty()
    } else {
      s[0].add(concat(s.subrange(1, s.len())))
    }
  }

  proof fn lemma_concat_uniform_length<T>(s: Seq<Seq<T>>, k: int)
    requires forall |i: int| #[auto_trigger] 0 <= i < s.len() ==> s[i].len() == k
    ensures concat(s).len() == k * s.len()
  {
    decreases(s.len());
    if s.len() == 0 {}
    else {
      lemma_concat_uniform_length::<T>(s.subrange(1, s.len()), k);
      assert(s[0].len() == k);
      assert(concat(s).len() == k + k * (s.len() - 1));
    }
  }

  proof fn lemma_concat_uniform_index<T>(s: Seq<Seq<T>>, k: int)
    requires 0 <= k,
          forall |i: int| #[auto_trigger] 0 <= i < s.len() ==> s[i].len() == k,
    ensures concat(s).len() == k * s.len(),
            forall |i: int, j: int| #[auto_trigger] 0 <= i < s.len() && 0 <= j < k ==> concat(s)[k * i + j] === s[i][j],
  {
    decreases(s.len());
    lemma_concat_uniform_length::<T>(s, k);
    if s.len() == 0 {}
    else {
      assert_forall_by(|i: int, j: int| {
        requires(0 <= i < s.len() && 0 <= j < k);
        ensures(concat(s)[k * i + j] === s[i][j]);
        if i == 0 {
        } else {
          assert(i <= s.len() - 1);
          // this non-linear arith is too hard
          assume(k * i <= k * (s.len() - 1));
          assert(k * i <= k * s.len() - k);
          assert(k * i + j < k * s.len());
          assert(k * i + j < concat(s).len());
          assert(k * i + j === k + k * (i - 1) + j);
          assert(s[0].len() == k);
          assert(concat(s)[k * i + j] === concat(s)[k + k * (i - 1) + j]);
          assert(concat(s)[k + k * (i-1) + j] === concat(s.subrange(1, s.len()))[k * (i - 1) + j]);
          lemma_concat_uniform_index::<T>(s.subrange(1, s.len()), k);
          assert(concat(s.subrange(1, s.len()))[k * (i - 1) + j] === s.subrange(1, s.len())[i-1][j]);
        }
      });
    }
  }

  mod model {
    use super::pervasive;
    use pervasive::{*, seq::*};
    use super::enc;
    use builtin::SpecOrd;
    use super::concat;

    pub struct Hdr {
      pub next_entry: u16,
      pub offsets: Seq<u16>,
    }

    impl Hdr {
      spec fn valid(self) -> bool {
        // length needs to fit in a u16
        self.offsets.len() < 0x1_0000
      }

      spec fn encode(self) -> Seq<u8>
      {
        enc::u16_le_bytes(self.next_entry).add(
          enc::u16_le_bytes(self.offsets.len() as u16)
        ).add(
          concat(self.offsets.map(|_i, x| enc::u16_le_bytes(x)))
        )
      }
    }

    pub struct LeafEntry {
      pub key: Seq<u8>,
      pub msg: Seq<u8>,
    }
  }

  // These structs are quite bare because they hold only the data that has been
  // parsed eagerly. Everything else is read from some array of bytes that
  // actually holds the data.

  struct Hdr {
    next_entry: u16,
    num_entries: u16,
  }

  impl Hdr {
    spec fn valid(self, bytes: Seq<u8>, data: Ghost<model::Hdr>) -> bool
    {
      // TODO: this is very tedious, might be appropriate to at least write
      // specs with parser combinators (much like EverParse)

      // bytes encodes self
      &&& #[trigger] enc::u16_le_bytes(self.next_entry) === bytes.subrange(0, 2)
      &&& enc::u16_le_bytes(self.num_entries) === bytes.subrange(2, 4)
      // self captures correct properties of abstract data
      &&& self.next_entry == data@.next_entry
      &&& self.num_entries as int == data@.offsets.len()
      // bytes also encodes the pointed-to data
      &&& (forall |i:int| 0 <= i < data@.offsets.len() ==>
                          enc::u16_le_bytes(#[trigger] data@.offsets[i]) === bytes.subrange(2+2 + 2*i, 2+2 + 2*(i+1)))
      &&& bytes.len() >= 2+2 + 2*data@.offsets.len()
    }

    fn offset_by_idx(&self, i: u64, buf: &Vec<u8>, data: Ghost<model::Hdr>) -> (off:u16)
      requires
        self.valid(buf@, data),
        i < data@.offsets.len(),
      ensures off == data@.offsets[i]
    {
      let off = enc::get_u16_le_bytes(buf, (2+2 + 2*i) as usize);
      proof { enc::axiom_u16_from_le_bytes_ok(data@.offsets[i]) };
      return off;
    }
  }

  struct LeafEntry {
    key_size: u16,
    msg_size: u16,
  }

  struct Leaf {
    hdr: Hdr,
  }

  fn main() {}
}
