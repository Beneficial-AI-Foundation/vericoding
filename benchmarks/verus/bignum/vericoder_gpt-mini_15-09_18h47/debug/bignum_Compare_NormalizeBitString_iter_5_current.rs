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
/* helper modified by LLM (iteration 5): convert char to bit */
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
    /* code modified by LLM (iteration 5): normalize leading zeros and compare sequences with trigger annotations */
    let n1: usize = s1.len();
    let n2: usize = s2.len();

    let mut p1: usize = 0;
    while p1 < n1 && s1[p1] == '0'
        invariant
            0 <= p1 as int && p1 as int <= n1 as int,
            forall |i: int| 0 <= i && i < p1 as int ==> #[trigger] s1@[i] == '0',
        decreases n1 - p1
    {
        p1 += 1;
    }

    let mut p2: usize = 0;
    while p2 < n2 && s2[p2] == '0'
        invariant
            0 <= p2 as int && p2 as int <= n2 as int,
            forall |i: int| 0 <= i && i < p2 as int ==> #[trigger] s2@[i] == '0',
        decreases n2 - p2
    {
        p2 += 1;
    }

    let len1: usize = n1 - p1;
    let len2: usize = n2 - p2;

    if len1 < len2 {
        return -1;
    } else if len1 > len2 {
        return 1;
    } else {
        let mut k: usize = 0;
        while k < len1
            invariant
                0 <= k as int && k as int <= len1 as int,
                forall |i: int| 0 <= i && i < k as int ==> #[trigger] s1@[(p1 as int + i)] == #[trigger] s2@[(p2 as int + i)],
            decreases len1 - k
        {
            let b1 = s1[p1 + k];
            let b2 = s2[p2 + k];
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


