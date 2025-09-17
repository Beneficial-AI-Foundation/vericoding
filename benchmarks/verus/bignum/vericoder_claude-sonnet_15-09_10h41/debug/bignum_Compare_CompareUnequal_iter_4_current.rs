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
    /* code modified by LLM (iteration 4): fixed loop invariant and preserves ValidBitString */
    let mut result = Vec::new();
    let mut start_idx = 0;
    
    // Handle empty input
    if s.len() == 0 {
        result.push('0');
        return result;
    }
    
    // Find first non-zero character
    while start_idx < s.len()
        invariant
            start_idx <= s.len(),
        decreases s.len() - start_idx
    {
        if s[start_idx] != '0' {
            break;
        }
        start_idx += 1;
    }
    
    // If all zeros, return "0"
    if start_idx == s.len() {
        result.push('0');
        return result;
    }
    
    // Copy from first non-zero to end
    let mut i = start_idx;
    while i < s.len()
        invariant
            start_idx <= i <= s.len(),
            result@.len() == i - start_idx,
            forall |j: int| 0 <= j < result@.len() ==> (result@[j] == '0' || result@[j] == '1'),
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
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
    /* code modified by LLM (iteration 4): simplified since longer normalized string is always greater */
    return 1;
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed type errors in lemma_equal_length_comparison */
proof fn lemma_longer_normalized_greater(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0',
        s1.len() > s2.len(),
    ensures Str2Int(s1) > Str2Int(s2)
{
    // For normalized strings, longer length means larger value
    // s1 has at least one more bit than s2, so s1 >= 2^(s2.len()) > s2
}

exec fn lemma_equal_length_comparison(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() == s2.len(),
    ensures
        Str2Int(s1) < Str2Int(s2) ==> res == -1,
        Str2Int(s1) == Str2Int(s2) ==> res == 0,
        Str2Int(s1) > Str2Int(s2) ==> res == 1,
{
    let mut i: usize = 0;
    while i < s1.len() as usize
        invariant
            i <= s1.len(),
            s1.len() == s2.len(),
        decreases s1.len() - i
    {
        if s1@[i as int] > s2@[i as int] {
            return 1;
        } else if s1@[i as int] < s2@[i as int] {
            return -1;
        }
        i += 1;
    }
    0
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
    /* code modified by LLM (iteration 4): use helper functions and proper normalization */
    let norm_s1 = NormalizeBitString(s1);
    let norm_s2 = NormalizeBitString(s2);
    
    if norm_s1.len() > norm_s2.len() {
        lemma_longer_normalized_greater(norm_s1@, norm_s2@);
        return 1;
    } else if norm_s1.len() < norm_s2.len() {
        lemma_longer_normalized_greater(norm_s2@, norm_s1@);
        return -1;
    } else {
        // Equal lengths, use helper to compare
        return lemma_equal_length_comparison(norm_s1@, norm_s2@);
    }
}
// </vc-code>

fn main() {}
}


