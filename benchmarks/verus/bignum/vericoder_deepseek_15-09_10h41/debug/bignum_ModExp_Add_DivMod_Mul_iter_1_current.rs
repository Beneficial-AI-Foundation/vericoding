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
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut res = Vec::<char>::new();
    let mut carry = 0;
    
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i && i <= max_len,
            ValidBitString(res@),
            Str2Int(res@) + carry * Exp_int(2, i as nat) == 
                Str2Int(s1.subrange(0, i as int)) + Str2Int(s2.subrange(0, i as int)),
        decreases max_len - i
    {
        let bit1 = if i < len1 { if s1[i as int] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < len2 { if s2[i as int] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        carry = if sum >= 2 { 1 } else { 0 };
        let res_bit = if sum % 2 == 1 { '1' } else { '0' };
        res.push(res_bit);
        i += 1;
    }
    
    if carry == 1 {
        res.push('1');
    }
    
    res
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
    let mut quotient = Vec::<char>::new();
    let mut remainder = dividend.to_vec();
    
    let divisor_val = Str2Int(divisor@);
    
    let mut pos = 0;
    let mut current_val = 0;
    
    while pos < remainder.len() as int
        invariant
            0 <= pos && pos <= remainder.len() as int,
            ValidBitString(remainder@),
            Str2Int(remainder@) == Str2Int(dividend@) % divisor_val,
            ValidBitString(quotient@),
            Str2Int(quotient@) * divisor_val + current_val == Str2Int(dividend.subrange(0, pos))
        decreases remainder.len() as int - pos
    {
        current_val = current_val * 2 + (if remainder[pos as usize] == '1' { 1 } else { 0 });
        
        if current_val >= divisor_val {
            quotient.push('1');
            current_val -= divisor_val;
        } else if quotient.len() > 0 {
            quotient.push('0');
        }
        
        pos += 1;
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    // Convert remainder to proper binary string
    let mut rem_str = Vec::<char>::new();
    let mut temp = current_val;
    while temp > 0
        invariant
            temp >= 0,
            Str2Int(rem_str@) == temp
        decreases temp
    {
        if temp % 2 == 1 {
            rem_str.insert(0, '1');
        } else {
            rem_str.insert(0, '0');
        }
        temp /= 2;
    }
    
    if rem_str.len() == 0 {
        rem_str.push('0');
    }
    
    (quotient, rem_str)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let len1 = s1.len();
    let len2 = s2.len();
    let mut result = Vec::<char>::new();
    
    // Initialize result with zeros
    for _ in 0..(len1 + len2) {
        result.push('0');
    }
    
    let mut i = len2 as int - 1;
    while i >= 0
        invariant
            -1 <= i && i < len2 as int,
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(s2.subrange(i + 1, len2 as int))
        decreases i + 1
    {
        if s2[i as usize] == '1' {
            // Add s1 to the result at appropriate position
            let mut carry = 0;
            let mut j = len1 as int - 1;
            while j >= 0
                invariant
                    -1 <= j && j < len1 as int,
                    carry >= 0 && carry <= 1
                decreases j + 1
            {
                let pos = len1 as int + i - j;
                let current_bit = if result[pos as usize] == '1' { 1 } else { 0 };
                let s1_bit = if s1[j as usize] == '1' { 1 } else { 0 };
                let sum = current_bit + s1_bit + carry;
                carry = if sum >= 2 { 1 } else { 0 };
                result[pos as usize] = if sum % 2 == 1 { '1' } else { '0' };
                j -= 1;
            }
            if carry == 1 {
                result[(len1 as int + i + 1) as usize] = '1';
            }
        }
        i -= 1;
    }
    
    // Remove leading zeros
    let mut start = result.len() - 1;
    while start > 0 && result[start] == '0' {
        result.pop();
        start -= 1;
    }
    
    result.reverse();
    result
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = Str2Int(sx@);
    let modulus = Str2Int(sz@);
    let bit_length = sy.len();
    
    let mut result = vec!['1'];
    let mut base = sx.to_vec();
    
    let mut i = (bit_length - 1) as int;
    while i >= 0
        invariant
            -1 <= i && i < bit_length as int,
            ValidBitString(result@),
            ValidBitString(base@),
            Str2Int(result@) == Exp_int(x, Str2Int(sy.subrange(i + 1, bit_length as int))) % modulus,
            Str2Int(base@) == Exp_int(x, Exp_int(2, (bit_length as int - i - 1) as nat)) % modulus
        decreases i + 1
    {
        // Square the result
        let squared = Mul(&result, &result);
        let squared_mod = DivMod(&squared, sz).0;
        result = DivMod(&squared_mod, sz).1;
        
        if sy[i as usize] == '1' {
            // Multiply by base
            let multiplied = Mul(&result, &base);
            let multiplied_mod = DivMod(&multiplied, sz).0;
            result = DivMod(&multiplied_mod, sz).1;
        }
        
        // Square the base for next iteration
        let base_squared = Mul(&base, &base);
        let base_squared_mod = DivMod(&base_squared, sz).0;
        base = DivMod(&base_squared_mod, sz).1;
        
        i -= 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
