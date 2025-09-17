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
/* helper modified by LLM (iteration 8): no additional helpers needed for this implementation */
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
    /* code modified by LLM (iteration 8): fixed index out of bound issues by using int for loop index and safe subtraction */
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let max_len_int = max_len as int;
    let len1_int = len1 as int;
    let len2_int = len2 as int;
    let diff1 = (max_len_int - len1_int) as usize;
    let diff2 = (max_len_int - len2_int) as usize;
    let mut i = 0int;
    while i < max_len_int
        invariant
            0 <= i <= max_len_int,
        decreases
            max_len_int - i,
    {
        let b1 = if i >= (diff1 as int) {
            let idx = (i - (diff1 as int)) as usize;
            s1[idx]
        } else {
            '0'
        };
        let b2 = if i >= (diff2 as int) {
            let idx = (i - (diff2 as int)) as usize;
            s2[idx]
        } else {
            '0'
        };
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


