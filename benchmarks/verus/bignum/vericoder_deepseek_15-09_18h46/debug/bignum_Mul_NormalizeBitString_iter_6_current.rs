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
/* helper modified by LLM (iteration 6): Adding missing pad_with_zeros helper function */
fn pad_with_zeros(mut s: Vec<char>, target_len: usize) -> (res: Vec<char>)
    requires
        target_len >= s.len(),
        ValidBitString(s@),
    ensures
        ValidBitString(res@),
        res.len() == target_len,
        forall |i: int| 0 <= i && i < s.len() ==> res@[i] == s@[i],
        forall |i: int| s.len() <= i && i < target_len ==> res@[i] == '0',
        Str2Int(res@) == Str2Int(s@)
{
    while s.len() < target_len
        invariant
            ValidBitString(s@),
            s.len() <= target_len,
            Str2Int(s@) == Str2Int(old(s)),
        decreases target_len - s.len()
    {
        s.push('0');
        proof {
            assert(ValidBitString(s@));
            assert(Str2Int(s@) == 2 * Str2Int(old(s@)) + 0);
        }
    }
    s
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): Fixed compilation error by using new pad_with_zeros helper */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    
    let s1_padded = pad_with_zeros(s1.to_vec(), max_len);
    let s2_padded = pad_with_zeros(s2.to_vec(), max_len);
    
    let mut result = Vec::<char>::new();
    
    for i in 0..max_len {
        let bit1 = s1_padded[i];
        let bit2 = s2_padded[i];
        
        if bit1 == '1' && bit2 == '1' {
            result.push('1');
        } else {
            result.push('0');
        }
    }
    
    proof {
        lemma_str2int_zero();
        lemma_str2int_nonnegative(s1@);
        lemma_str2int_nonnegative(s2@);
        lemma_str2int_monotonic(s1@, s1_padded@);
        lemma_str2int_monotonic(s2@, s2_padded@);
    }
    
    result
}
// </vc-code>

fn main() {}
}
