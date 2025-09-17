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
/* helper modified by LLM (iteration 5): fixed postcondition by making length bound conditional on empty input */
exec fn normalize_helper(s: &[char], start_idx: usize) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
        start_idx <= s@.len(),
    ensures
        ValidBitString(res@),
        res@.len() >= 1,
        (start_idx < s@.len() ==> res@.len() <= s@.len() - start_idx) &&
        (start_idx == s@.len() ==> res@.len() == 1),
{
    let mut result = Vec::new();
    let mut i = start_idx;
    
    while i < s.len()
        invariant
            start_idx <= i,
            i <= s@.len(),
            ValidBitString(s@),
            ValidBitString(result@),
            result@.len() == i - start_idx,
            forall |j: int| 0 <= j < result@.len() ==> result@[j] == s@[start_idx + j],
        decreases s@.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    
    if result.len() == 0 {
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(start_idx == s@.len());
        }
    } else {
        proof {
            assert(result@.len() == s@.len() - start_idx);
            assert(start_idx < s@.len());
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using helper function with conditional postcondition */
    let result = normalize_helper(s, 0);
    result
}
// </vc-code>

fn main() {}
}
