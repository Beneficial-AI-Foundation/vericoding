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
// No helper lemmas required for this proof.
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
  let n1: int = s1.len() as int;
  let n2: int = s2.len() as int;

  // Compute integer value of s1
  let mut i1: int = 0;
  let mut v1: nat = 0;
  while i1 < n1
    invariant 0 <= i1 && i1 <= n1,
    invariant v1 == Str2Int(s1@.subrange(0, i1)),
    decreases n1 - i1
  {
    let c: char = s1[i1 as usize];
    if c == '1' {
      v1 = 2 * v1 + 1;
    } else {
      v1 = 2 * v1;
    }
    proof {
      // runtime char equals spec-level char at the same index
      assert(c == s1@.index(i1));
      // by the definition of Str2Int on a non-empty sequence:
      // Str2Int(subrange(0, i1+1)) == 2*Str2Int(subrange(0, i1)) + bit_at_i1
      assert(
        Str2Int(s1@.subrange(0, i1 + 1))
          == 2 * Str2Int(s1@.subrange(0, i1))
             + (if s1@.index(i1) == '1' { 1nat } else { 0nat })
      );
      // thus v1 equals Str2Int of the extended prefix
      assert(v1 == Str2Int(s1@.subrange(0, i1 + 1)));
    }
    i1 += 1;
  }

  // Compute integer value of s2
  let mut i2: int = 0;
  let mut v2: nat = 0;
  while i2 < n2
    invariant 0 <= i2 && i2 <= n2,
    invariant v2 == Str2Int(s2@.subrange(0, i2)),
    decreases n2 - i2
  {
    let c: char = s2[i2 as usize];
    if c == '1' {
      v2 = 2 * v2 + 1;
    } else {
      v2 = 2 * v2;
    }
    proof {
      assert(c == s2@.index(i2));
      assert(
        Str2Int(s2@.subrange(0, i2 + 1))
          == 2 * Str2Int(s2@.subrange(0, i2))
             + (if s2@.index(i2) == '1' { 1nat } else { 0nat })
      );
      assert(v2 == Str2Int(s2@.subrange(0, i2 + 1)));
    }
    i2 += 1;
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