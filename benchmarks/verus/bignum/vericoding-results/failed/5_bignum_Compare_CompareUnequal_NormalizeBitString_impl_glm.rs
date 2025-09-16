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

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fix NormalizeBitString implementation */
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    
    // Skip leading zeros
    while i < s.len() && s[i] == '0'
        invariant 0 <= i <= s.len(),
        forall |j: int| 0 <= j < i ==> s@[j] == '0',
        decreases s.len() - i
    {
        i += 1;
    }
    
    // If we skipped all characters, the string was all zeros, so return "0"
    if i == s.len() {
        result.push('0');
    } else {
        // Copy the remaining characters
        while i < s.len()
            invariant i <= s.len(),
            decreases s.len() - i
        {
            result.push(s[i]);
            i += 1;
        }
    }
    
    result
}
// </vc-code>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
   s1@.len() > 0,
   (s1@.len() > 1 ==> s1@[0] != '0'),
   s2@.len() > 0,
   (s2@.len() > 1 ==> s2@[0] != '0'),
   s1@.len() > s2@.len(),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): CompareUnequal implementation */
    // Since s1 is longer than s2 and both are normalized (no leading zeros),
    // s1 must represent a larger number than s2.
    1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fix CompareEqualLength to use proper indexing */
exec fn CompareEqualLength(s1: &[char], s2: &[char]) -> (res: i32)
    requires ValidBitString(s1@),
    ValidBitString(s2@),
    s1@.len() == s2@.len(),
    ensures
        Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
        Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
        Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
    decreases s1@.len()
{
    if s1.len() == 0 {
        0
    } else if s1[s1.len() - 1] < s2[s2.len() - 1] {
        -1
    } else if s1[s1.len() - 1] > s2[s2.len() - 1] {
        1
    } else {
        let s1_sub = &s1[0..(s1.len() - 1)];
        let s2_sub = &s2[0..(s2.len() - 1)];
        CompareEqualLength(s1_sub, s2_sub)
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
    /* code modified by LLM (iteration 3): Compare implementation */
    let normalized_s1 = NormalizeBitString(s1);
    let normalized_s2 = NormalizeBitString(s2);
    
    if normalized_s1.len() > normalized_s2.len() {
        1
    } else if normalized_s1.len() < normalized_s2.len() {
        -1
    } else {
        // Equal length, use the helper function
        CompareEqualLength(&normalized_s1, &normalized_s2)
    }
}
// </vc-code>

fn main() {}
}


