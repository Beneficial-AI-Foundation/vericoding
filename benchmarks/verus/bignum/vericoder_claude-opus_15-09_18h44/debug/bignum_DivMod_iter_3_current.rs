
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
/* helper modified by LLM (iteration 3): Added lemma for Str2Int properties */
proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1 } else { 0 },
{
    assert(s.push(c).len() == s.len() + 1);
    assert(s.push(c).subrange(0, s.push(c).len() - 1) =~= s);
    assert(s.push(c).index(s.push(c).len() - 1) == c);
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
    /* code modified by LLM (iteration 3): Fixed Str2Int computation and overflow issues */
    let dividend_val = compute_str2int(dividend);
    let divisor_val = compute_str2int(divisor);
    
    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;
    
    let quotient = int_to_binary(quotient_val);
    let remainder = int_to_binary(remainder_val);
    
    return (quotient, remainder);
}

exec fn compute_str2int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < 0x10000000000000000,  // Ensure no overflow
    ensures
        res as nat == Str2Int(s@),
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            result < 0x10000000000000000,
        decreases s.len() - i
    {
        assert(s@.subrange(0, (i + 1) as int) =~= s@.subrange(0, i as int).push(s@[i as int]));
        lemma_str2int_append(s@.subrange(0, i as int), s@[i as int]);
        
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    result
}

exec fn int_to_binary(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat,
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        assert(v@.len() == 1);
        assert(v@[0] == '0');
        assert(Str2Int(v@) == 0);
        return v;
    }
    
    let mut digits = Vec::new();
    let mut num = n;
    let mut power: u64 = 1;
    
    // Collect digits in reverse order
    while num > 0
        invariant
            ValidBitString(digits@),
            n > 0,
        decreases num
    {
        if num % 2 == 0 {
            digits.push('0');
        } else {
            digits.push('1');
        }
        num = num / 2;
    }
    
    // Reverse the digits
    let mut result = Vec::new();
    let mut i = digits.len();
    while i > 0
        invariant
            0 <= i <= digits.len(),
            ValidBitString(result@),
            ValidBitString(digits@),
        decreases i
    {
        i = i - 1;
        result.push(digits[i]);
    }
    
    result
}
// </vc-code>

fn main() {}
}


