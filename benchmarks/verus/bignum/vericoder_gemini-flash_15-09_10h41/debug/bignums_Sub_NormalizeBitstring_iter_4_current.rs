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
/* helper modified by LLM (iteration 4): No changes */
spec fn TrimLeadingZeros(s: Seq<char>) -> Seq<char>
    recommends ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 {
        s
    } else if s.index(0) == '0' {
        TrimLeadingZeros(s.subrange(1, s.len() as int))
    } else {
        s
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Cast 0 to `usize` for comparison with `len()` */
{
    let trimmed_s = TrimLeadingZeros(s@);
    let final_s = if trimmed_s.len() == (0 as usize) { Seq::empty().push('0') } else { trimmed_s };
    
    let mut result_vec = Vec::<char>::new();
    let mut i = 0;
    while i < final_s.len()
        invariant
            0 <= i && i <= final_s.len(),
            result_vec.len() == i,
            forall |j: int| 0 <= j && j < i ==> result_vec.get_Permission(j).is_Some() && result_vec@[j] == final_s@[j],
            ValidBitString(result_vec@),
    {
        result_vec.push(final_s@[i]);
        i = i + 1;
    }
    
    proof {
        assert(ValidBitString(final_s));
    }
    
    result_vec
}
// </vc-code>

fn main() {}
}
