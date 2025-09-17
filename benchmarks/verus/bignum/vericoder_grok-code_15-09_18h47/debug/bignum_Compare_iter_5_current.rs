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
    /* code modified by LLM (iteration 5): replaced .min() with manual if to fix exec mode error */
    let len1 = s1.len();
    let len2 = s2.len();
    let min_len = if len1 <= len2 { len1 } else { len2 };
    let mut i = 0;
    while i < min_len
        invariant
            0 <= i <= min_len,
        decreases
            min_len - i
    {
        if s1[i] != s2[i] {
            if s1[i] == '1' {
                return 1;
            } else {
                return -1;
            }
        }
        i = i + 1;
    }
    if len1 == len2 {
        return 0;
    } else if len1 > len2 {
        while i < len1
            invariant
                0 <= i <= len1,
                len2 <= i,
            decreases
                len1 - i
        {
            if s1[i] == '1' {
                return 1;
            }
            i = i + 1;
        }
        return 0;
    } else {
        while i < len2
            invariant
                0 <= i <= len2,
                len1 <= i,
            decreases
                len2 - i
        {
            if s2[i] == '1' {
                return -1;
            }
            i = i + 1;
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


