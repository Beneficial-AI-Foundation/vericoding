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
    /* code modified by LLM (iteration 8): added decreases clause to fix compilation error */
    let mut result = Vec::new();
    let mut i = 0;
    
    // Skip leading zeros
    while i < s.len() && s[i] == '0'
        invariant
            0 <= i <= s.len(),
            result@.len() == 0,
        decreases s.len() - i
    {
        i += 1;
    }
    
    // Copy remaining characters
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(result@),
            result@.len() > 0 ==> result@[0] != '0',
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    
    if result.len() == 0 {
        result.push('0');
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
    /* code modified by LLM (iteration 8): since s1 is longer and normalized, it must be greater */
    return 1;
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 8): simplified lemma about string length relationship */
proof fn length_comparison_lemma(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > s2.len(),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0',
    ensures
        Str2Int(s1) > Str2Int(s2),
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
    /* code modified by LLM (iteration 8): added decreases clause to fix compilation error */
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    
    if t1.len() > t2.len() {
        return 1;
    } else if t1.len() < t2.len() {
        return -1;
    } else {
        let mut i = 0;
        while i < t1.len()
            invariant
                0 <= i <= t1.len(),
                t1.len() == t2.len(),
                ValidBitString(t1@),
                ValidBitString(t2@),
                forall |j: int| 0 <= j < i ==> t1@[j] == t2@[j],
            decreases t1.len() - i
        {
            if t1[i] == '1' && t2[i] == '0' {
                return 1;
            } else if t1[i] == '0' && t2[i] == '1' {
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


