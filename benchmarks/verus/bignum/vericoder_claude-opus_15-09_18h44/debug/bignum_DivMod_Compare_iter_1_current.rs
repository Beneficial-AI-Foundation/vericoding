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
exec fn div_mod_binary(dividend: nat, divisor: nat) -> (nat, nat)
    requires divisor > 0
    ensures |res| == (dividend / divisor, dividend % divisor)
{
    let mut quotient = 0nat;
    let mut remainder = dividend;
    
    while remainder >= divisor
        invariant
            dividend == quotient * divisor + remainder,
            remainder >= 0,
        decreases remainder
    {
        quotient = quotient + 1;
        remainder = remainder - divisor;
    }
    
    (quotient, remainder)
}

exec fn nat_to_binary(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
        Str2Int(res@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    
    let mut result = Vec::new();
    let mut num = n;
    
    while num > 0
        invariant
            ValidBitString(result@),
            n == num * vstd::arithmetic::power2::pow2((result.len()) as nat) + Str2Int(result@),
        decreases num
    {
        if num % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        num = num / 2;
    }
    
    // Reverse the result
    let mut reversed = Vec::new();
    let mut i = result.len();
    while i > 0
        invariant
            ValidBitString(reversed@),
            i <= result.len(),
        decreases i
    {
        i = i - 1;
        reversed.push(result[i]);
    }
    
    reversed
}

exec fn binary_to_nat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut result = 0nat;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    result
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
    let dividend_nat = binary_to_nat(dividend);
    let divisor_nat = binary_to_nat(divisor);
    
    let (quotient_nat, remainder_nat) = div_mod_binary(dividend_nat, divisor_nat);
    
    let quotient_vec = nat_to_binary(quotient_nat);
    let remainder_vec = nat_to_binary(remainder_nat);
    
    (quotient_vec, remainder_vec)
}
// </vc-code>

fn main() {}
}

