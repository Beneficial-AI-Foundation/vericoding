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
/* helper modified by LLM (iteration 3): replaced to_vec() with manual vector creation */
spec fn divmod_invariant(dividend: Seq<char>, divisor: Seq<char>, quotient: Seq<char>, remainder: Seq<char>) -> bool {
    ValidBitString(quotient) && ValidBitString(remainder) &&
    Str2Int(dividend) == Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder) &&
    Str2Int(remainder) < Str2Int(divisor)
}

spec fn is_greater_or_equal(a: Seq<char>, b: Seq<char>) -> bool {
    Str2Int(a) >= Str2Int(b)
}

exec fn subtract_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@), Str2Int(a@) >= Str2Int(b@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(a@) - Str2Int(b@)
{
    let mut result = Vec::new();
    let mut borrow = 0;
    let mut i = a.len();
    
    while i > 0
        invariant
            ValidBitString(result@),
            i <= a.len()
    {
        i -= 1;
        let digit_a = if a[i] == '1' { 1 } else { 0 };
        let digit_b = if i < b.len() && b[i] == '1' { 1 } else { 0 };
        
        let diff = digit_a - digit_b - borrow;
        if diff >= 0 {
            result.push(if diff == 1 { '1' } else { '0' });
            borrow = 0;
        } else {
            result.push('1');
            borrow = 1;
        }
    }
    
    let mut reversed = Vec::new();
    let mut j = result.len();
    while j > 0
        invariant
            ValidBitString(reversed@)
    {
        j -= 1;
        reversed.push(result[j]);
    }
    
    reversed
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): replaced to_vec() with manual vector creation */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    let mut i = 0;
    while i < dividend.len()
        invariant
            ValidBitString(remainder@),
            i <= dividend.len()
    {
        remainder.push(dividend[i]);
        i += 1;
    }
    
    while remainder.len() > 0 && Str2Int(remainder@) >= Str2Int(divisor@)
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(dividend@) == Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(remainder@)
    {
        if is_greater_or_equal(remainder@, divisor@) {
            remainder = subtract_binary(&remainder, divisor);
            if quotient.len() == 0 {
                quotient.push('1');
            } else {
                let mut carry = 1;
                let mut j = quotient.len();
                while j > 0 && carry > 0
                    invariant
                        ValidBitString(quotient@)
                {
                    j -= 1;
                    if quotient[j] == '0' {
                        quotient.set(j, '1');
                        carry = 0;
                    } else {
                        quotient.set(j, '0');
                    }
                }
                if carry > 0 {
                    quotient.insert(0, '1');
                }
            }
        } else {
            break;
        }
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    if remainder.len() == 0 {
        remainder.push('0');
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

