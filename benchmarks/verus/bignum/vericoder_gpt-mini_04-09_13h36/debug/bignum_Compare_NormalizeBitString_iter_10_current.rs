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
exec fn seq_to_nat(s: &[char]) -> (r: nat)
  requires ValidBitString(s@)
  ensures Str2Int(s@) == r
  decreases s.len()
{
  if s.len() == 0 {
    return 0nat;
  } else {
    let prefix = &s[..s.len()-1];
    let acc: nat = seq_to_nat(prefix);
    let b = s[s.len()-1];
    if b == '1' {
      return 2nat * acc + 1nat;
    } else {
      return 2nat * acc;
    }
  }
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
  let n1: nat = seq_to_nat(s1);
  let n2: nat = seq_to_nat(s2);
  if n1 < n2 {
    return -1i32;
  } else if n1 == n2 {
    return 0i32;
  } else {
    return 1i32;
  }
}
// </vc-code>

fn main() {}
}