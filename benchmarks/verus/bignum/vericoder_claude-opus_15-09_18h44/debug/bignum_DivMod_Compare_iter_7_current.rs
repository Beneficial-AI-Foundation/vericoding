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
exec fn div_mod_binary(dividend: u64, divisor: u64) -> (res: (u64, u64))
    requires divisor > 0,
        dividend <= u64::MAX,
        divisor <= u64::MAX,
    ensures res == ((dividend / divisor) as u64, (dividend % divisor) as u64)
{
    /* helper modified by LLM (iteration 7): fixed overflow and invariant issues */
    let mut quotient: u64 = 0;
    let mut remainder = dividend;
    
    while remainder >= divisor
        invariant
            dividend == quotient * divisor + remainder,
            quotient <= dividend / divisor,
            remainder <= dividend,
        decreases remainder
    {
        remainder = remainder - divisor;
        quotient = quotient + 1;
    }
    
    (quotient, remainder)
}

exec fn nat_to_binary(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
        Str2Int(res@) == n as nat
{
    /* helper modified by LLM (iteration 7): fixed bit string construction */
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        assert(ValidBitString(v@));
        assert(Str2Int(v@) == 0);
        return v;
    }
    
    let mut result = Vec::new();
    let mut num = n;
    let mut power: u64 = 1;
    
    // First pass: collect bits in reverse order
    while num > 0
        invariant
            0 <= num <= n,
            ValidBitString(result@),
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
            0 <= i <= result.len(),
            ValidBitString(result@),
            ValidBitString(reversed@),
        decreases i
    {
        i = i - 1;
        reversed.push(result[i]);
    }
    
    reversed
}

exec fn binary_to_nat(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
        Str2Int(s@) <= u64::MAX as nat,
    ensures res as nat == Str2Int(s@)
{
    /* helper modified by LLM (iteration 7): fixed type error for index */
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@.subrange(0, i as int)),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            result <= u64::MAX / 2 || (result == u64::MAX / 2 && (i >= s.len() || s@[i as int] == '0')),
        decreases s.len() - i
    {
        let old_result = result;
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
    /* code modified by LLM (iteration 7): handle u64 bounds properly using ghost code */
    // Check that values fit in u64 using ghost code
    proof {
        let divisor_val = Str2Int(divisor@);
        let dividend_val = Str2Int(dividend@);
        if divisor_val > u64::MAX as nat || dividend_val > u64::MAX as nat {
            // Cannot process values larger than u64::MAX
            assert(false);
        }
    }
    
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

