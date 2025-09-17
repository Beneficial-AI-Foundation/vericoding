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
    let mut result = Vec::new();
    let mut start_idx = 0;
    
    // Find first non-zero character
    while start_idx < s.len()
        invariant
            0 <= start_idx <= s.len(),
            ValidBitString(s@),
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
            ValidBitString(s@),
            ValidBitString(result@),
            result@.len() == i - start_idx,
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
    // Since s1 is longer than s2 and both are normalized,
    // s1 represents a larger number
    return 1;
}
// </vc-code>

// <vc-helpers>
proof fn lemma_longer_string_larger(s1: Seq<char>, s2: Seq<char>)
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
}

proof fn lemma_same_length_lexicographic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        s1.len() > 0,
    ensures
        (forall |i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]) ==> Str2Int(s1) == Str2Int(s2)
{
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
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    
    if t1.len() > t2.len() {
        proof {
            lemma_longer_string_larger(t1@, t2@);
        }
        return 1;
    } else if t1.len() < t2.len() {
        proof {
            lemma_longer_string_larger(t2@, t1@);
        }
        return -1;
    } else {
        // Same length, compare lexicographically
        let mut i = 0;
        while i < t1.len()
            invariant
                0 <= i <= t1.len(),
                t1.len() == t2.len(),
                forall |j: int| 0 <= j < i ==> t1@[j] == t2@[j],
        {
            if t1[i] > t2[i] {
                return 1;
            } else if t1[i] < t2[i] {
                return -1;
            }
            i += 1;
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


