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
spec fn effective_start(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else if s.index(0) == '0' {
    1 + effective_start(s.subrange(1, s.len() as int))
  } else {
    0
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
/* code modified by LLM (iteration 10): fixed type mismatch by using usize for exec variables instead of int */
{
    let mut starts1: usize = 0;
    while starts1 < s1.len() && s1[starts1] == '0' {
        starts1 += 1;
    }
    let mut starts2: usize = 0;
    while starts2 < s2.len() && s2[starts2] == '0' {
        starts2 += 1;
    }
    let len1 = s1.len() - starts1;
    let len2 = s2.len() - starts2;
    if len1 < len2 {
        return -1;
    } else if len1 > len2 {
        return 1;
    } else {
        let mut i: usize = 0;
        while i < len1 {
            if s1[starts1 + i] == '0' && s2[starts2 + i] == '1' {
                return -1;
            } else if s1[starts1 + i] == '1' && s2[starts2 + i] == '0' {
                return 1;
            }
            i += 1;
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


