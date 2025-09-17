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
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 2): Changed Seq<char> to &[char] for verification */
spec fn is_all_zeros(s: &[char]) -> bool {
    forall |i: int| 0 <= i && i < s.len() ==> s.index(i) == '0'
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix compilation errors regarding int/usize mismatch and .index() calls for &[char] by casting to `int` and importing std::ops::Index. */
{
    use std::ops::Index;

    let mut i: int = 0;
    while i < s.len() as int - 1
        invariant
            0 <= i,
            i <= s.len() as int - 1,
            ValidBitString(s@),
            forall |j: int| 0 <= j && j < i ==> s.index(j as usize) == '0',
        decreases s.len() as int - i
    {
        if s.index(i as usize) == '1' {
            break;
        }
        i = i + 1;
    }
    let mut res = Vec::<char>::new();
    let mut k: int = i;
    while k < s.len() as int
        invariant
            i <= k,
            k <= s.len() as int,
            ValidBitString(s@),
            res@.len() as int == (k - i) as int,
            forall |idx: int| 0 <= idx && idx < k - i ==> res@[idx] == s.index((i + idx) as usize),
            res@.len() >= 0,
        decreases s.len() as int - k
    {
        res.push(s.index(k as usize));
        k = k + 1;
    }
    if res.len() == 0 {
        res.push('0');
    }
    res
}
// </vc-code>

fn main() {}
}
