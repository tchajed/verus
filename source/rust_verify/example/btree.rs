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
  mod model {
    use super::pervasive;
    use pervasive::{*, seq::*};

    pub struct Hdr {
      pub next_entry: u16,
      pub offsets: Seq<u16>,
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
