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
/* helper modified by LLM (iteration 5): fixed array bounds checks and improved verification logic */
exec fn add_bit_strings(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@),
{
    if s1.len() == 0 && s2.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = Vec::new();
    let mut carry = 0;
    let mut i = s1.len();
    let mut j = s2.len();
    
    while i > 0 || j > 0 || carry > 0
        invariant
            carry <= 1,
            i <= s1.len(),
            j <= s2.len(),
        decreases i + j + carry
    {
        let bit1 = if i > 0 && i <= s1.len() { if s1[i-1] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if j > 0 && j <= s2.len() { if s2[j-1] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    let mut final_result = Vec::new();
    for k in 0..result.len()
        invariant
            ValidBitString(final_result@),
    {
        final_result.push(result[result.len() - 1 - k]);
    }
    
    proof {
        assert(ValidBitString(final_result@));
    }
    
    final_result
}

exec fn shift_left(s: &[char], positions: usize) -> (res: Vec<char>)
    requires ValidBitString(s@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@) * nat_pow(2, positions as nat),
{
    let mut result = Vec::new();
    
    for i in 0..s.len()
        invariant
            ValidBitString(result@),
    {
        result.push(s[i]);
    }
    
    for _ in 0..positions
        invariant
            ValidBitString(result@),
    {
        result.push('0');
    }
    
    proof {
        assert(ValidBitString(result@));
    }
    
    result
}

spec fn nat_pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * nat_pow(base, (exp - 1) as nat) }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified empty string handling */
    if s1.len() == 0 || s2.len() == 0 {
        let mut res = vec!['0'];
        proof {
            assert(ValidBitString(res@));
            assert(Str2Int(res@) == 0);
        }
        return res;
    }
    
    let mut result = vec!['0'];
    
    for i in 0..s2.len()
        invariant
            ValidBitString(result@),
            ValidBitString(s1@),
    {
        if s2[s2.len() - 1 - i] == '1' {
            proof {
                assert(ValidBitString(s1@));
            }
            let shifted = shift_left(s1, i);
            result = add_bit_strings(&result, &shifted);
        }
    }
    
    proof {
        assert(ValidBitString(result@));
    }
    
    result
}
// </vc-code>

fn main() {}
}
