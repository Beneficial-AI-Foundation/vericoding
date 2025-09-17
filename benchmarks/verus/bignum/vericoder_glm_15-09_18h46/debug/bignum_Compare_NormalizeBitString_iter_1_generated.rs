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
spec fn bit_char_to_int(c: char) -> int
{
  if c == '0' {
    0
  } else {
    1
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
  let len1 = s1.len();
  let len2 = s2.len();
  
  // Compare lengths first
  if len1 < len2 {
    return -1;
  } else if len1 > len2 {
    return 1;
  }
  
  // If lengths are equal, compare character by character
  let mut i = 0;
  while i < len1
      invariant
          0 <= i <= len1,
          forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
      decreases len1 - i
  {
    if s1[i] != s2[i] {
      if s1[i] == '0' {
        return -1;
      } else {
        return 1;
      }
    }
    i += 1;
  }
  
  // If we reach here, the strings are equal
  return 0;
}
// </vc-code>

fn main() {}
}


