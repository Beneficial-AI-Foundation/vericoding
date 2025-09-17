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
/* helper modified by LLM (iteration 2): Add helper for comparing bit strings */
spec fn CompareBitStrings(s1: Seq<char>, s2: Seq<char>) -> int
    recommends ValidBitString(s1), ValidBitString(s2)
    decreases s1.len() + s2.len()
{
    if s1.len() < s2.len() {
        -1
    } else if s1.len() > s2.len() {
        1
    } else if s1.len() == 0 {
        0
    } else {
        let last1 = s1.index(s1.len() as int - 1);
        let last2 = s2.index(s2.len() as int - 1);
        let rest_compare = CompareBitStrings(
            s1.subrange(0, s1.len() as int - 1),
            s2.subrange(0, s2.len() as int - 1)
        );
        if rest_compare != 0 {
            rest_compare
        } else {
            if last1 == last2 {
                0
            } else if last1 == '0' {
                -1
            } else {
                1
            }
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
/* code modified by LLM (iteration 2): Compare bit strings by length and then character by character */
{
    let len1 = s1.len();
    let len2 = s2.len();
    
    // Compare lengths first - shorter string represents smaller number
    if len1 < len2 {
        return -1;
    } else if len1 > len2 {
        return 1;
    }
    
    // If lengths are equal, compare character by character from left to right
    let mut i = 0;
    while i < len1
        invariant
            0 <= i <= len1,
            len1 == len2,
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


