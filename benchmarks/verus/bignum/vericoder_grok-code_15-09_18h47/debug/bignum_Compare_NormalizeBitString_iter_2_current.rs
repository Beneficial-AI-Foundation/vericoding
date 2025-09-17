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
  requires ValidBitString(s)
  ensures
    0 <= effective_start(s) && effective_start(s) <= s.len(),
    forall |i: int| 0 <= i && i < effective_start(s) ==> s.index(i) == '0',
    effective_start(s) < s.len() ==> s.index(effective_start(s) as int) == '1'
{
  let mut i = 0;
  while i < s.len() && s.index(i as int) == '0' {
    i += 1;
  }
  i
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
    /* code modified by LLM (iteration 2): fixed type casting errors by using usize subtraction instead of casting to int */
    let len1 = s1.len();
    let len2 = s2.len();
    let mut start1 = 0;
    while start1 < len1 && s1[start1] == '0' {
        start1 += 1;
    }
    let mut start2 = 0;
    while start2 < len2 && s2[start2] == '0' {
        start2 += 1;
    }
    let eff_len1 = len1 - start1;
    let eff_len2 = len2 - start2;
    if eff_len1 < eff_len2 {
        return -1;
    } else if eff_len1 > eff_len2 {
        return 1;
    } else {
        let mut i = 0;
        while i < eff_len1 {
            if s1[start1 + i] != s2[start2 + i] {
                if s1[start1 + i] == '0' {
                    return -1;
                } else {
                    return 1;
                }
            }
            i += 1;
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


