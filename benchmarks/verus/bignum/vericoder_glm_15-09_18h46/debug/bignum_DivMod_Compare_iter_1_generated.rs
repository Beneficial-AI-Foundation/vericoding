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
spec fn reversed_str_to_int(s: Seq<char>) -> nat
    requires ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s.index(0) == '1' { 1 } else { 0 }) 
        + 2 * reversed_str_to_int(s.subrange(1, s.len() as int))
    }
}

exec fn str_to_int(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut result = 0;
    for i in 0..s.len() {
        let c = s[i];
        result = result * 2;
        if c == '1' {
            result = result + 1;
        }
    }
    result
}

exec fn int_to_str(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == n
{
    if n == 0 {
        return vec!['0'];
    }
    let mut digits = Vec::new();
    let mut num = n;
    while num > 0
        invariant
            num >= 0,
            n == num * (2 as nat).pow(digits.len() as nat) + reversed_str_to_int(digits@),
        decreases num
    {
        if num % 2 == 0 {
            digits.push('0');
        } else {
            digits.push('1');
        }
        num = num / 2;
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
    let dividend_int = str_to_int(dividend);
    let divisor_int = str_to_int(divisor);
    let quotient_int = dividend_int / divisor_int;
    let remainder_int = dividend_int % divisor_int;
    let quotient_str = int_to_str(quotient_int);
    let remainder_str = int_to_str(remainder_int);
    (quotient_str, remainder_str)
}
// </vc-code>

fn main() {}
}

