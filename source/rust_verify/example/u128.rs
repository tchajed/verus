#![allow(unused_imports)]
/// u128 library

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;

verus! {
  // 2^64
  const POW64: int = 0x1_0000_0000_0000_0000;
  // 2^128 - 1
  // (can't be 2^128 because integer literals must fit in a u128)
  const U128_MAX: int = 0xffff_ffff_ffff_ffff__ffff_ffff_ffff_ffff;

  const U64_MAX: u64 = 0xffff_ffff_ffff_ffff;

  proof fn sanity_check()
    ensures
      U128_MAX == POW64 * POW64 - 1,
      U64_MAX == POW64 - 1,
  {
  }

  #[derive(PartialEq, Eq, Structural)]
  struct U128 { lo: u64, hi: u64 }

  fn u64_add_carry(x: u64, y: u64) -> (c:u64)
    ensures (x as int + y as int) >= POW64 <==> c == 1,
            (x as int + y as int) < POW64 <==> c == 0,
  {
    // x + y <= U64_MAX
    if (y <= U64_MAX - x) {
      0
    } else {
      1
    }
  }

  fn u64_wrap_add(x: u64, y: u64) -> (r:u64)
    ensures r == (x + y) % 64
  {
    assume(false);
    // TODO: how do I do intentionally wrapping arithmetic?
    x + y
  }

  impl U128 {
    spec fn view(self) -> int {
      self.lo + self.hi * POW64
    }

    fn add(&self, other: &Self) -> Self
      requires self@ + other@ <= U128_MAX
    {
      let r = U128 {
        lo: u64_wrap_add(self.lo, other.lo),
        hi: u64_add_carry(self.hi, other.hi) + self.hi + other.hi,
      };
      r
    }
  }

  fn main() {}
}
