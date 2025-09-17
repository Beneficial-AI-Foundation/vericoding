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
/* helper modified by LLM (iteration 7): Add decreases clause to recursive lemma */
proof fn compare_lemma(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2),
    ensures Str2Int(s1) < Str2Int(s2) ==> Str2Int(s1) + 1 <= Str2Int(s2),
        Str2Int(s1) > Str2Int(s2) ==> Str2Int(s2) + 1 <= Str2Int(s1)
    decreases s1.len() + s2.len()
{
    if s1.len() > 0 && s2.len() > 0 {
        let s1_prefix = s1.subrange(0, s1.len() - 1);
        let s2_prefix = s2.subrange(0, s2.len() - 1);
        compare_lemma(s1_prefix, s2_prefix);
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
/* code modified by LLM (iteration 7): Add proper loop invariant and decreases clause */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let mut i = 0usize;
    
    while i < len1 && i < len2
        invariant
            0 <= i && i <= len1 && i <= len2,
            ValidBitString(s1@),
            ValidBitString(s2@),
        decreases (len1 - i) + (len2 - i)
    {
        if s1[i] == '1' && s2[i] == '0' {
            return 1;
        } else if s1[i] == '0' && s2[i] == '1' {
            return -1;
        }
        i += 1;
    }
    
    if len1 < len2 {
        -1
    } else if len1 > len2 {
        1
    } else {
        0
    }
}
// </vc-code>

fn main() {}
}


