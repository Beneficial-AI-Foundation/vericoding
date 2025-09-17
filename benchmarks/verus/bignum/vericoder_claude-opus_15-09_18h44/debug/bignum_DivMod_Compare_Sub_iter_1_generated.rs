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
exec fn compare_binary(a: &[char], b: &[char]) -> (res: bool)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
    ensures
        res == (Str2Int(a@) >= Str2Int(b@)),
{
    let mut i = 0;
    let len_a = a.len();
    let len_b = b.len();
    
    if len_a > len_b {
        return true;
    } else if len_a < len_b {
        return false;
    }
    
    while i < len_a
        invariant
            0 <= i <= len_a,
            len_a == len_b,
            ValidBitString(a@),
            ValidBitString(b@),
            forall |j: int| 0 <= j && j < i ==> a@[j] == b@[j],
    {
        if a[i] == '1' && b[i] == '0' {
            return true;
        } else if a[i] == '0' && b[i] == '1' {
            return false;
        }
        i = i + 1;
    }
    true
}

exec fn subtract_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
        Str2Int(a@) >= Str2Int(b@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) - Str2Int(b@),
{
    let mut result = Vec::new();
    let mut borrow = 0u8;
    let mut i = 0;
    let len_a = a.len();
    let len_b = b.len();
    
    while i < len_a
        invariant
            0 <= i <= len_a,
            ValidBitString(a@),
            ValidBitString(b@),
            ValidBitString(result@),
            borrow == 0 || borrow == 1,
    {
        let digit_a = if a[i] == '1' { 1u8 } else { 0u8 };
        let digit_b = if i < len_b { if b[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        
        let mut diff = digit_a as i8 - digit_b as i8 - borrow as i8;
        if diff < 0 {
            diff = diff + 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        
        result.push(if diff == 1 { '1' } else { '0' });
        i = i + 1;
    }
    
    while result.len() > 1 && result[result.len() - 1] == '0'
        invariant
            result.len() >= 1,
            ValidBitString(result@),
    {
        result.pop();
    }
    
    result
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
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
    }
    
    if !compare_binary(&remainder, divisor) {
        quotient.push('0');
        return (quotient, remainder);
    }
    
    let mut temp_dividend = Vec::new();
    let mut idx = 0;
    
    while idx < dividend.len()
        invariant
            0 <= idx <= dividend.len(),
            ValidBitString(quotient@),
            ValidBitString(temp_dividend@),
            ValidBitString(divisor@),
            Str2Int(divisor@) > 0,
    {
        temp_dividend.push(dividend[idx]);
        
        while temp_dividend.len() > 1 && temp_dividend[0] == '0'
            invariant
                temp_dividend.len() >= 1,
                ValidBitString(temp_dividend@),
        {
            temp_dividend.remove(0);
        }
        
        if compare_binary(&temp_dividend, divisor) {
            quotient.push('1');
            temp_dividend = subtract_binary(&temp_dividend, divisor);
        } else if quotient.len() > 0 {
            quotient.push('0');
        }
        
        idx = idx + 1;
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    if temp_dividend.len() == 0 {
        temp_dividend.push('0');
    }
    
    (quotient, temp_dividend)
}
// </vc-code>

fn main() {}
}

