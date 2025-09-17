use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed nat and int literal syntax errors by removing invalid suffixes */
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i = 0;
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    
    while i <= max_len
        invariant
            i <= max_len + 1,
            carry == 0 || carry == 1,
            ValidBitString(result@),
            result.len() == i
    {
        let bit1 = if i < len1 { if s1[len1 - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < len2 { if s2[len2 - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        result.push(result_bit);
        i += 1;
        if carry == 0 && i > len1 && i > len2 {
            break;
        }
    }
    
    let mut final_result = Vec::<char>::new();
    let mut j = result.len();
    while j > 0
        invariant
            j <= result.len(),
            ValidBitString(final_result@)
    {
        j -= 1;
        final_result.push(result[j]);
    }
    
    if final_result.len() == 0 {
        final_result.push('0');
    }
    
    final_result
}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed nat literal syntax errors by removing invalid suffixes */
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);
    
    if dividend_val == 0 {
        let zero = vec!['0'];
        return (zero.clone(), zero);
    }
    
    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;
    
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    if quotient_val == 0 {
        quotient.push('0');
    } else {
        let mut temp_q = quotient_val;
        while temp_q > 0
            invariant
                ValidBitString(quotient@)
        {
            if temp_q % 2 == 1 {
                quotient.push('1');
            } else {
                quotient.push('0');
            }
            temp_q = temp_q / 2;
        }
        quotient.reverse();
    }
    
    if remainder_val == 0 {
        remainder.push('0');
    } else {
        let mut temp_r = remainder_val;
        while temp_r > 0
            invariant
                ValidBitString(remainder@)
        {
            if temp_r % 2 == 1 {
                remainder.push('1');
            } else {
                remainder.push('0');
            }
            temp_r = temp_r / 2;
        }
        remainder.reverse();
    }
    
    (quotient, remainder)
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed int and nat literal syntax errors by removing invalid suffixes */
    if n == 0 {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let sy_val = Str2Int(sy@);
    if sy_val == 0 {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let sx_val = Str2Int(sx@);
    let sz_val = Str2Int(sz@);
    
    let mut base = sx_val % sz_val;
    let mut exp = sy_val;
    let mut result_val = 1;
    
    while exp > 0
        invariant
            sz_val > 1,
            base < sz_val,
            result_val < sz_val
    {
        if exp % 2 == 1 {
            result_val = (result_val * base) % sz_val;
        }
        base = (base * base) % sz_val;
        exp = exp / 2;
    }
    
    let mut result = Vec::<char>::new();
    if result_val == 0 {
        result.push('0');
    } else {
        let mut temp = result_val;
        while temp > 0
            invariant
                ValidBitString(result@)
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp = temp / 2;
        }
        result.reverse();
    }
    
    result
}
// </vc-code>

fn main() {}
}


