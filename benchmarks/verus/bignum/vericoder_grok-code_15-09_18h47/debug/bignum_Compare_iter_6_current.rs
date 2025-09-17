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
/**
 * helper modified by LLM (iteration 6): no helpers needed for this implementation
 */
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
    /* code modified by LLM (iteration 6): implemented comparison by aligning bit strings on the left with '0' padding */
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut i = 0usize;
    while i < max_len
        invariant
            0 <= i <= max_len,
        decreases
            max_len - i
    {
        let j1 = i as int - (max_len as int - len1 as int);
        let b1 = if j1 >= 0 { s1[j1 as usize] } else { '0' };
        let j2 = i as int - (max_len as int - len2 as int);
        let b2 = if j2 >= 0 { s2[j2 as usize] } else { '0' };
        if b1 != b2 {
            if b1 == '1' {
                return 1;
            } else {
                return -1;
            }
        }
        i = i + 1;
    }
    return 0;
}
// </vc-code>

fn main() {}
}


