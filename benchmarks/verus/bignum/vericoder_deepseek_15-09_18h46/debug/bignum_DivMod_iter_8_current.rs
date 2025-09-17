
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
/* helper modified by LLM (iteration 8): Fixed syntax error in lemma signature */
proof fn helper_lemma_binary_conversion_valid(n: nat)
    decreases n
    ensures ValidBitString(nat_to_binary_digits(n))
{
    if n > 0 {
        helper_lemma_binary_conversion_valid(n / 2);
    }
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
/* code modified by LLM (iteration 8): Fixed compilation error */
{
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    let mut current_dividend = dividend.to_vec();
    
    while current_dividend.len() > 0
        invariant
            ValidBitString(current_dividend@),
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(dividend@) == Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(remainder@ + current_dividend@),
            0 <= Str2Int(remainder@) < Str2Int(divisor@)
        decreases current_dividend.len()
    {
        let bit = current_dividend.remove(0);
        remainder.push(bit);
        
        if Str2Int(remainder@) >= Str2Int(divisor@) {
            quotient.push('1');
            let remainder_value = Str2Int(remainder@);
            let divisor_value = Str2Int(divisor@);
            let remainder_nat = remainder_value % divisor_value;
            
            proof {
                helper_lemma_div_mod_properties(remainder_value, divisor_value);
                helper_lemma_binary_conversion_valid(remainder_nat);
                helper_lemma_binary_conversion_value(remainder_nat);
            }
            
            remainder.clear();
            let remainder_digits = nat_to_binary_digits(remainder_nat);
            
            proof {
                let len = remainder_digits.len() as int;
                for i in 0..len
                    invariant
                        forall |j: int| 0 <= j && j < i ==> remainder_digits@.index(j) == remainder_digits@.index(j)
                {
                }
            }
            
            ghost {
                let len = remainder_digits.len() as int;
                for i in 0..len
                    invariant
                        forall |j: int| 0 <= j && j < i ==> remainder@.index(j) == remainder_digits@.index(j)
                {
                    remainder.push(remainder_digits@.index(i));
                }
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


