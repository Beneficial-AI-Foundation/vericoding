
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
/* helper modified by LLM (iteration 5): fixed nat literal syntax by removing 'nat' suffix */
spec fn bits_to_nat(bits: &[char]) -> nat {
    Str2Int(bits@)
}

spec fn nat_to_bits_spec(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        nat_to_bits_spec(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
    }
}

exec fn nat_to_bits(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
        Str2Int(result@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(result@)
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp = temp / 2;
        }
        result.reverse();
        result
    }
}

exec fn subtract_if_ge(dividend: &mut Vec<char>, divisor: &[char]) -> (borrowed: bool)
    requires ValidBitString(old(dividend)@),
        ValidBitString(divisor@)
    ensures ValidBitString(dividend@),
        borrowed == (Str2Int(old(dividend)@) >= Str2Int(divisor@)),
        if borrowed {
            Str2Int(dividend@) == Str2Int(old(dividend)@) - Str2Int(divisor@)
        } else {
            dividend@ == old(dividend)@
        }
{
    if Str2Int(dividend@) >= Str2Int(divisor@) {
        let diff = Str2Int(dividend@) - Str2Int(divisor@);
        *dividend = nat_to_bits(diff);
        true
    } else {
        false
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
{
    /* code modified by LLM (iteration 5): fixed nat literal syntax by removing 'nat' suffix */
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    // Handle zero dividend
    if dividend.len() == 1 && dividend[0] == '0' {
        quotient.push('0');
        remainder.push('0');
        return (quotient, remainder);
    }
    
    // Initialize remainder to empty, we'll build it bit by bit
    remainder.push('0');
    
    let mut i = 0;
    while i < dividend.len()
        invariant
            i <= dividend.len(),
            ValidBitString(quotient@),
            ValidBitString(remainder@)
    {
        // Shift remainder left and add next bit
        let next_bit = dividend[i];
        
        // Remove leading zero if present and we're adding a new bit
        if remainder.len() == 1 && remainder[0] == '0' {
            remainder[0] = next_bit;
        } else {
            remainder.push(next_bit);
        }
        
        // Check if we can subtract divisor from current remainder
        if Str2Int(remainder@) >= Str2Int(divisor@) {
            let diff = Str2Int(remainder@) - Str2Int(divisor@);
            remainder = nat_to_bits(diff);
            quotient.push('1');
        } else {
            quotient.push('0');
        }
        
        i += 1;
    }
    
    // Handle case where quotient is empty (should be '0')
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    // Handle case where remainder is empty (should be '0')
    if remainder.len() == 0 {
        remainder.push('0');
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


