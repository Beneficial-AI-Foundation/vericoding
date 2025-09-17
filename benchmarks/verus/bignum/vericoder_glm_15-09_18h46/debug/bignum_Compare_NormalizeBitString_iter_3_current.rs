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
/* code modified by LLM (iteration 3): Skip leading zeros and compare remaining parts */
{
    // Skip leading zeros in s1
    let mut i = 0;
    while i < s1.len() && s1[i] == '0'
        invariant 0 <= i <= s1.len()
        decreases s1.len() - i
    {
        i += 1;
    }
    let start1 = i;
    let len1_remaining = s1.len() - start1;

    // Skip leading zeros in s2
    let mut j = 0;
    while j < s2.len() && s2[j] == '0'
        invariant 0 <= j <= s2.len()
        decreases s2.len() - j
    {
        j += 1;
    }
    let start2 = j;
    let len2_remaining = s2.len() - start2;

    // Compare the lengths of the remaining parts
    if len1_remaining < len2_remaining {
        return -1;
    } else if len1_remaining > len2_remaining {
        return 1;
    }

    // Now compare the remaining parts bit by bit
    let mut k = 0;
    while k < len1_remaining
        invariant
            0 <= k <= len1_remaining,
            len1_remaining == len2_remaining,
            forall |m: int| 0 <= m && m < k ==> s1@[start1 + m] == s2@[start2 + m],
        decreases len1_remaining - k
    {
        if s1[start1 + k] != s2[start2 + k] {
            if s1[start1 + k] == '0' {
                return -1;
            } else {
                return 1;
            }
        }
        k += 1;
    }

    return 0;
}
// </vc-code>

fn main() {}
}


