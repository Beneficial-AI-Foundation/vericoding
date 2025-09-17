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
exec fn bit_string_to_nat(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
{
    let mut val = 0nat;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            val == Str2Int(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        val = val * 2;
        if s[i] == '1' {
            val = val + 1;
        }
        i = i + 1;
    }
    val
}

exec fn nat_to_bit_string(mut n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
        Str2Int(result@) == n
{
    if n == 0 {
        return vec!['0'];
    }
    let mut digits = Vec::new();
    while n > 0
        invariant ValidBitString(digits@)
        decreases n
    {
        if n % 2 == 0 {
            digits.push('0');
        } else {
            digits.push('1');
        }
        n = n / 2;
    }
    digits.reverse();
    digits
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let dividend_val = bit_string_to_nat(dividend);
    let divisor_val = bit_string_to_nat(divisor);
    
    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;
    
    let quotient = nat_to_bit_string(quotient_val);
    let remainder = nat_to_bit_string(remainder_val);
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

