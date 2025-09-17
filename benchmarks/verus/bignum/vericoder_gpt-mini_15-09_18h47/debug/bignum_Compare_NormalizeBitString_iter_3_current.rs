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
/* helper modified by LLM (iteration 3): convert char to bit */
spec fn CharToBit(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }
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
    /* code modified by LLM (iteration 3): skip leading zeros with decreases and then lexicographically compare */
    let n1: int = s1.len() as int;
    let n2: int = s2.len() as int;

    let mut p1: int = 0;
    while p1 < n1 && s1[p1 as usize] == '0'
        invariant
            0 <= p1 && p1 <= n1,
            forall |i: int| 0 <= i && i < p1 ==> s1[i as usize] == '0',
        decreases n1 - p1
    {
        p1 += 1;
    }

    let mut p2: int = 0;
    while p2 < n2 && s2[p2 as usize] == '0'
        invariant
            0 <= p2 && p2 <= n2,
            forall |i: int| 0 <= i && i < p2 ==> s2[i as usize] == '0',
        decreases n2 - p2
    {
        p2 += 1;
    }

    let len1: int = n1 - p1;
    let len2: int = n2 - p2;

    if len1 < len2 {
        return -1;
    } else if len1 > len2 {
        return 1;
    } else {
        let mut k: int = 0;
        while k < len1
            invariant
                0 <= k && k <= len1,
                forall |i: int| 0 <= i && i < k ==> s1[(p1 + i) as usize] == s2[(p2 + i) as usize],
            decreases len1 - k
        {
            let b1 = s1[(p1 + k) as usize];
            let b2 = s2[(p2 + k) as usize];
            if b1 != b2 {
                if b1 == '1' {
                    return 1;
                } else {
                    return -1;
                }
            }
            k += 1;
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


