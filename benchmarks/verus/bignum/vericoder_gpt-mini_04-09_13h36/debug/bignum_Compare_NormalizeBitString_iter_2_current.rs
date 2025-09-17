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
exec fn seq_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures Str2Int(s@) == result
  decreases s.len()
{
  let mut acc: nat = 0;
  let mut i: int = 0;
  while i < s.len() as int
    invariant 0 <= i && i <= s.len() as int;
    invariant acc == Str2Int(s@.subrange(0, i));
    decreases s.len() as int - i;
  {
    let b = s[i as usize];
    if b == '1' {
      acc = 2 * acc + 1;
    } else {
      // Since ValidBitString(s@) holds, b must be '0' here.
      acc = 2 * acc;
    }
    i += 1;
  }
  acc
}
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
  let n1 = seq_to_nat(s1);
  let n2 = seq_to_nat(s2);
  if n1 < n2 {
    return -1;
  } else if n1 == n2 {
    return 0;
  } else {
    return 1;
  }
}
// </vc-code>

fn main() {}
}