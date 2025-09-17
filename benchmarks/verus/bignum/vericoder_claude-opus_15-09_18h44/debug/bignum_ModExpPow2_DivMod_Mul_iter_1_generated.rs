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
{{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    if dividend.len() == 0 {
        quotient.push('0');
        remainder.push('0');
        return (quotient, remainder);
    }
    
    let mut current = Vec::new();
    let mut i = 0;
    
    while i < dividend.len() {
        current.push(dividend[i]);
        
        // Remove leading zeros
        while current.len() > 1 && current[0] == '0' {
            current.remove(0);
        }
        
        // Check if current >= divisor
        let mut can_divide = false;
        if current.len() > divisor.len() {
            can_divide = true;
        } else if current.len() == divisor.len() {
            let mut j = 0;
            can_divide = true;
            while j < current.len() {
                if current[j] < divisor[j] {
                    can_divide = false;
                    break;
                } else if current[j] > divisor[j] {
                    break;
                }
                j += 1;
            }
        }
        
        if can_divide {
            quotient.push('1');
            // Subtract divisor from current
            let mut new_current = Vec::new();
            let mut borrow = 0;
            let mut k = current.len() as i32 - 1;
            let mut l = divisor.len() as i32 - 1;
            
            while k >= 0 || l >= 0 || borrow != 0 {
                let mut val = if k >= 0 { if current[k as usize] == '1' { 1 } else { 0 } } else { 0 };
                val -= if l >= 0 { if divisor[l as usize] == '1' { 1 } else { 0 } } else { 0 };
                val -= borrow;
                
                if val < 0 {
                    val += 2;
                    borrow = 1;
                } else {
                    borrow = 0;
                }
                
                new_current.insert(0, if val == 1 { '1' } else { '0' });
                k -= 1;
                l -= 1;
            }
            
            current = new_current;
        } else {
            quotient.push('0');
        }
        
        i += 1;
    }
    
    // Remove leading zeros from quotient
    while quotient.len() > 1 && quotient[0] == '0' {
        quotient.remove(0);
    }
    
    // Remove leading zeros from remainder
    while current.len() > 1 && current[0] == '0' {
        current.remove(0);
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    if current.len() == 0 {
        current.push('0');
    }
    
    remainder = current;
    return (quotient, remainder);
}}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{{
    let mut result = Vec::new();
    result.push('0');
    
    let mut i = 0;
    while i < s1.len() {
        if s1[i] == '1' {
            // Add s2 shifted by (s1.len() - 1 - i) positions
            let mut carry = 0;
            let shift = s1.len() - 1 - i;
            
            // Extend result if needed
            while result.len() < s2.len() + shift {
                result.insert(0, '0');
            }
            
            let mut j = s2.len() as i32 - 1;
            let mut k = result.len() as i32 - 1 - shift as i32;
            
            while j >= 0 || carry != 0 {
                let mut sum = carry;
                if j >= 0 {
                    sum += if s2[j as usize] == '1' { 1 } else { 0 };
                }
                if k >= 0 && k < result.len() as i32 {
                    sum += if result[k as usize] == '1' { 1 } else { 0 };
                }
                
                if k >= 0 && k < result.len() as i32 {
                    result[k as usize] = if sum % 2 == 1 { '1' } else { '0' };
                } else if k < 0 {
                    result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
                    k += 1;
                }
                
                carry = sum / 2;
                j -= 1;
                k -= 1;
            }
        }
        i += 1;
    }
    
    // Remove leading zeros
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    return result;
}}
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
{{
    if sy.len() == 0 || (sy.len() == 1 && sy[0] == '0') {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    
    if n == 0 {
        // sy = 1
        let (_, remainder) = DivMod(sx, sz);
        return remainder;
    }
    
    // Compute sy/2 (right shift)
    let mut sy_half = Vec::new();
    let mut i = 0;
    while i < sy.len() - 1 {
        sy_half.push(sy[i]);
        i += 1;
    }
    
    // Recursive call with n-1
    let half_result = ModExpPow2(sx, &sy_half, n - 1, sz);
    
    // Square the result
    let squared = Mul(&half_result, &half_result);
    
    // Take modulo
    let (_, result) = DivMod(&squared, sz);
    
    return result;
}}
// </vc-code>

fn main() {}
}
