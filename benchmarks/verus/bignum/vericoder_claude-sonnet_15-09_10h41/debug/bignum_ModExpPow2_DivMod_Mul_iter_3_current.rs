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
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed reversed iteration with manual loop */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
    }
    
    while remainder.len() > 0 && remainder[0] == '0' {
        remainder.remove(0);
    }
    
    if remainder.len() == 0 {
        remainder.push('0');
    }
    
    while Str2Int(remainder@) >= Str2Int(divisor@) {
        let mut temp_remainder = remainder.clone();
        let mut temp_divisor = Vec::<char>::new();
        
        for j in 0..divisor.len() {
            temp_divisor.push(divisor[j]);
        }
        
        while temp_divisor.len() < temp_remainder.len() {
            temp_divisor.push('0');
        }
        
        if Str2Int(temp_divisor@) > Str2Int(temp_remainder@) {
            temp_divisor.pop();
        }
        
        quotient.push('1');
        
        let mut borrow = 0;
        let mut new_remainder = Vec::<char>::new();
        
        let mut k = temp_remainder.len();
        while k > 0 {
            k = k - 1;
            let r_bit = if temp_remainder[k] == '1' { 1 } else { 0 };
            let d_bit = if k < temp_divisor.len() && temp_divisor[k] == '1' { 1 } else { 0 };
            
            let diff = r_bit - d_bit - borrow;
            if diff >= 0 {
                new_remainder.insert(0, if diff == 1 { '1' } else { '0' });
                borrow = 0;
            } else {
                new_remainder.insert(0, '1');
                borrow = 1;
            }
        }
        
        remainder = new_remainder;
        
        while remainder.len() > 0 && remainder[0] == '0' {
            remainder.remove(0);
        }
        
        if remainder.len() == 0 {
            remainder.push('0');
        }
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    (quotient, remainder)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): no changes needed for Mul */
    let mut result = Vec::<char>::new();
    result.push('0');
    
    for i in 0..s2.len() {
        if s2[s2.len() - 1 - i] == '1' {
            let mut shifted_s1 = Vec::<char>::new();
            
            for j in 0..s1.len() {
                shifted_s1.push(s1[j]);
            }
            
            for _ in 0..i {
                shifted_s1.push('0');
            }
            
            let mut carry = 0;
            let mut new_result = Vec::<char>::new();
            let max_len = if result.len() > shifted_s1.len() { result.len() } else { shifted_s1.len() };
            
            for k in 0..max_len {
                let r_bit = if k < result.len() { if result[result.len() - 1 - k] == '1' { 1 } else { 0 } } else { 0 };
                let s_bit = if k < shifted_s1.len() { if shifted_s1[shifted_s1.len() - 1 - k] == '1' { 1 } else { 0 } } else { 0 };
                
                let sum = r_bit + s_bit + carry;
                new_result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
                carry = sum / 2;
            }
            
            if carry > 0 {
                new_result.insert(0, '1');
            }
            
            result = new_result;
        }
    }
    
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    
    result
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
    /* code modified by LLM (iteration 3): fixed literal suffixes and type comparison */
    if n == 0 {
        if sy@.len() == 1 && sy@.index(0) == '1' {
            let mut result = Vec::<char>::new();
            result.push('1');
            return result;
        } else {
            let mut result = Vec::<char>::new();
            result.push('1');
            return result;
        }
    }
    
    if Str2Int(sy@) == 0 {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let mut half_y = Vec::<char>::new();
    let mut i = 0;
    while i < n {
        if i == 0 {
            half_y.push('1');
        } else {
            half_y.push('0');
        }
        i = i + 1;
    }
    
    let temp_result = ModExpPow2(sx, &half_y, n - 1, sz);
    let squared = Mul(&temp_result, &temp_result);
    
    let (_, remainder) = DivMod(&squared, sz);
    
    remainder
}
// </vc-code>

fn main() {}
}
