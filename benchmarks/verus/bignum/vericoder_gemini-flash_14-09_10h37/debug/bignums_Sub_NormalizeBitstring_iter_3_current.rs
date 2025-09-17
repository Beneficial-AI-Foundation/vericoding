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
/* helper modified by LLM (iteration 3): helper spec function */
spec fn is_all_zeros(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i && i < s.len() ==> s.index(i) == '0'
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation issue where `int` type was used in `exec` code for `start_index` and `s.len()`. Changed `start_index` to `usize` for indexing and `s.len()` to `usize` where appropriate. */
{
    let mut i: usize = 0;
    while i < s.len() && s[i] == '0'
        invariant
            0 <= i && i <= s.len()
    {
        i = i + 1;
    }

    let mut res_vec = Vec::<char>::new();
    let start_index: usize = i;

    if start_index == s.len() {
        res_vec.push('0');
        return res_vec;
    }

    // Copy the remaining characters
    let sub_seq = s@.subrange(start_index as int, s.len() as int);
    for j in start_index..s.len() {
        res_vec.push(s[j]);
    }

    res_vec
}
// </vc-code>

fn main() {}
}
