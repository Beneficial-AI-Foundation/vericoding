
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
/* helper modified by LLM (iteration 3): Fixed type conversion in proof helpers */
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
        dividend % divisor >= 0,
        dividend % divisor < divisor,
        dividend == divisor * (dividend / divisor) + dividend % divisor,
{
}

spec fn nat_to_binary_digits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let prev = nat_to_binary_digits(n / 2);
        let digit = if n % 2 == 1 { '1' } else { '0' };
        prev + Seq::new(1, digit)
    }
}

proof fn helper_lemma_nat_to_binary_valid(n: nat)
    ensures ValidBitString(nat_to_binary_digits(n)),
    decreases n
{
    if n > 0 {
        helper_lemma_nat_to_binary_valid(n / 2);
    }
}

proof fn helper_lemma_nat_to_binary_value(n: nat)
    ensures Str2Int(nat_to_binary_digits(n)) == n,
    decreases n
{
    if n > 0 {
        helper_lemma_nat_to_binary_value(n / 2);
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
/* code modified by LLM (iteration 3): Fixed type conversion in for-loop */
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
            0 <= Str2Int(remainder@) < Str2Int(divisor@),
        decreases current_dividend.len()
    {
        let bit = current_dividend.remove(0);
        remainder.push(bit);
        
        if Str2Int(remainder@) >= Str2Int(divisor@) {
            quotient.push('1');
            let remainder_value = Str2Int(remainder@);
            let remainder_nat = remainder_value % Str2Int(divisor@);
            
            proof {
                helper_lemma_div_mod_properties(remainder_value, Str2Int(divisor@));
                helper_lemma_nat_to_binary_valid(remainder_nat);
                helper_lemma_nat_to_binary_value(remainder_nat);
            }
            
            remainder.clear();
            let remainder_digits = nat_to_binary_digits(remainder_nat);
            for i in 0..remainder_digits.len() {
                remainder.push(remainder_digits[i as int]);
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


