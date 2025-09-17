
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
proof fn helper_lemma_valid_subrange(s: Seq<char>, start: int, end: int)
    requires
        ValidBitString(s),
        0 <= start <= end <= s.len(),
    ensures
        ValidBitString(s.subrange(start, end)),
{
    if start < end {
        helper_lemma_valid_subrange(s, start, end - 1);
    }
}

proof fn helper_lemma_str2int_nonnegative(s: Seq<char>)
    requires ValidBitString(s),
    ensures Str2Int(s) >= 0,
{
    if s.len() > 0 {
        helper_lemma_str2int_nonnegative(s.subrange(0, s.len() as int - 1));
    }
}

proof fn helper_lemma_div_mod_properties(dividend: nat, divisor: nat)
    requires divisor > 0,
    ensures
        divisor > 0,
        dividend % divisor >= 0,
        dividend % divisor < divisor,
        dividend == divisor * (dividend / divisor) + dividend % divisor,
{
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    let mut current_dividend = dividend.to_vec();
    
    while current_dividend.len() > 0
        invariant
            ValidBitString(current_dividend@),
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(dividend@) == Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(current_dividend@),
            0 <= Str2Int(remainder@) < Str2Int(divisor@),
        decreases current_dividend.len()
    {
        proof {
            helper_lemma_str2int_nonnegative(divisor@);
        }
        
        let bit = current_dividend.remove(0);
        remainder.push(bit);
        
        if Str2Int(remainder@) >= Str2Int(divisor@) {
            quotient.push('1');
            let current_remainder_value = Str2Int(remainder@);
            remainder.clear();
            let remainder_value = current_remainder_value % Str2Int(divisor@);
            
            proof {
                helper_lemma_div_mod_properties(current_remainder_value, Str2Int(divisor@));
            }
            
            let bits_remaining = format_int_base2(remainder_value);
            for b in bits_remaining.iter() {
                remainder.push(*b);
            }
        } else {
            quotient.push('0');
        }
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


