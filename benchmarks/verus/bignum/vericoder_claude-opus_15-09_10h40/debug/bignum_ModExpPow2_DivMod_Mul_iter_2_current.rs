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
{/* code modified by LLM (iteration 2): Fixed type mismatch by using 0int literal */
    if n == 0int {
        // y = 1 or y = 0
        if sy.len() > 0 && sy[0] == '1' {
            // y = 1, return x % z
            let (_, remainder) = DivMod(sx, sz);
            return remainder;
        } else {
            // y = 0, return 1 % z
            let one = vec!['1'];
            let (_, remainder) = DivMod(&one, sz);
            return remainder;
        }
    } else {
        // Recursive case: compute x^(y/2) mod z
        let mut half_y = Vec::<char>::new();
        for i in 0..sy.len() - 1 {
            half_y.push(sy[i]);
        }
        
        let half_result = ModExpPow2(sx, &half_y, (n - 1int) as int, sz);
        
        // Square the half_result
        let squared = Mul(&half_result, &half_result);
        let (_, squared_mod) = DivMod(&squared, sz);
        
        // Check if y is odd (last bit is 1)
        if sy.len() > 0 && sy[0] == '1' {
            // y is odd, multiply by x once more
            let product = Mul(&squared_mod, sx);
            let (_, result_mod) = DivMod(&product, sz);
            return result_mod;
        } else {
            // y is even
            return squared_mod;
        }
    }
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    // Convert input slices to working vectors
    let mut current_dividend = Vec::<char>::new();
    for i in 0..dividend.len() {
        current_dividend.push(dividend[i]);
    }
    
    let mut divisor_vec = Vec::<char>::new();
    for i in 0..divisor.len() {
        divisor_vec.push(divisor[i]);
    }
    
    // Simple binary division algorithm
    while current_dividend.len() > 0 && !(current_dividend.len() == 1 && current_dividend[0] == '0') {
        // Check if current_dividend >= divisor
        let mut can_subtract = false;
        if current_dividend.len() > divisor_vec.len() {
            can_subtract = true;
        } else if current_dividend.len() == divisor_vec.len() {
            let mut i = current_dividend.len();
            while i > 0 {
                i = i - 1;
                if current_dividend[i] > divisor_vec[i] {
                    can_subtract = true;
                    break;
                } else if current_dividend[i] < divisor_vec[i] {
                    break;
                }
            }
            if i == 0 && current_dividend[0] >= divisor_vec[0] {
                can_subtract = true;
            }
        }
        
        if can_subtract {
            quotient.push('1');
            // Subtract divisor from current_dividend
            let mut borrow = 0u8;
            let mut i = 0;
            while i < divisor_vec.len() || borrow > 0 {
                let dividend_digit = if i < current_dividend.len() {
                    if current_dividend[i] == '1' { 1u8 } else { 0u8 }
                } else { 0u8 };
                let divisor_digit = if i < divisor_vec.len() {
                    if divisor_vec[i] == '1' { 1u8 } else { 0u8 }
                } else { 0u8 };
                
                let mut diff = dividend_digit as i8 - divisor_digit as i8 - borrow as i8;
                if diff < 0 {
                    diff = diff + 2;
                    borrow = 1;
                } else {
                    borrow = 0;
                }
                
                if i < current_dividend.len() {
                    current_dividend.set(i, if diff == 1 { '1' } else { '0' });
                }
                i = i + 1;
            }
            
            // Remove leading zeros
            while current_dividend.len() > 1 && current_dividend[current_dividend.len() - 1] == '0' {
                current_dividend.pop();
            }
        } else {
            break;
        }
    }
    
    // What's left in current_dividend is the remainder
    if current_dividend.len() == 0 {
        remainder.push('0');
    } else {
        for i in 0..current_dividend.len() {
            remainder.push(current_dividend[i]);
        }
    }
    
    // Handle empty quotient
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    return (quotient, remainder);
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
    let mut result = Vec::<char>::new();
    result.push('0');
    
    for i in 0..s1.len() {
        if s1[i] == '1' {
            // Add s2 shifted by i positions
            let mut carry = 0u8;
            for j in 0..s2.len() + i {
                let s2_digit = if j >= i && j - i < s2.len() {
                    if s2[j - i] == '1' { 1u8 } else { 0u8 }
                } else { 0u8 };
                
                let result_digit = if j < result.len() {
                    if result[j] == '1' { 1u8 } else { 0u8 }
                } else { 0u8 };
                
                let sum = s2_digit + result_digit + carry;
                let new_digit = if sum % 2 == 1 { '1' } else { '0' };
                carry = sum / 2;
                
                if j < result.len() {
                    result.set(j, new_digit);
                } else {
                    result.push(new_digit);
                }
            }
            
            if carry > 0 {
                result.push('1');
            }
        }
    }
    
    return result;
}
// </vc-code>

fn main() {}
}
