use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
spec fn CharToBit(c: char) -> nat { if c == '1' { 1 } else { 0 } }
// </vc-helpers>

// <vc-spec>
exec fn Compare(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
  decreases Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut i1: int = 0;
    let mut v1: nat = 0;
    while i1 < s1.len() as int
        invariant
            0 <= i1 && i1 <= s1.len() as int,
            v1 == Str2Int(s1@.subrange(0, i1)),
        decreases s1.len() as int - i1
    {
        let idx = i1;
        let ch = s1[idx as usize];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        let old_v = v1;
        v1 = 2 * old_v + bit;
        i1 = idx + 1;
        proof {
            assert(old_v == Str2Int(s1@.subrange(0, idx)));
            assert(Str2Int(s1@.subrange(0, i1)) == 2 * Str2Int(s1@.subrange(0, idx)) + (if s1@.index(idx) == '1' { 1 } else { 0 }));
            assert(s1@.index(idx) == ch);
            assert(bit == (if s1@.index(idx) == '1' { 1 } else { 0 }));
            assert(v1 == Str2Int(s1@.subrange(0, i1)));
        }
    }

    let mut i2: int = 0;
    let mut v2: nat = 0;
    while i2 < s2.len() as int
        invariant
            0 <= i2 && i2 <= s2.len() as int,
            v2 == Str2Int(s2@.subrange(0, i2)),
        decreases s2.len() as int - i2
    {
        let idx = i2;
        let ch = s2[idx as usize];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        let old_v = v2;
        v2 = 2 * old_v + bit;
        i2 = idx + 1;
        proof {
            assert(old_v == Str2Int(s2@.subrange(0, idx)));
            assert(Str2Int(s2@.subrange(0, i2)) == 2 * Str2Int(s2@.subrange(0, idx)) + (if s2@.index(idx) == '1' { 1 } else { 0 }));
            assert(s2@.index(idx) == ch);
            assert(bit == (if s2@.index(idx) == '1' { 1 } else { 0 }));
            assert(v2 == Str2Int(s2@.subrange(0, i2)));
        }
    }

    if v1 < v2 {
        return -1;
    } else if v1 == v2 {
        return 0;
    } else {
        return 1;
    }
}

// </vc-code>

fn main() {}
}


