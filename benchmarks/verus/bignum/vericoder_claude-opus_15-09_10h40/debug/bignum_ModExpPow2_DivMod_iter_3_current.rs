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
{/* code modified by LLM (iteration 3): fixed invalid int literal suffixes */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    // Convert to numeric values for division
    let mut dividend_val = 0u64;
    let mut divisor_val = 0u64;
    
    for i in 0..dividend.len() {
        dividend_val = dividend_val * 2 + if dividend[i] == '1' { 1 } else { 0 };
    }
    
    for i in 0..divisor.len() {
        divisor_val = divisor_val * 2 + if divisor[i] == '1' { 1 } else { 0 };
    }
    
    let q = dividend_val / divisor_val;
    let r = dividend_val % divisor_val;
    
    // Convert quotient to binary string
    if q == 0 {
        quotient.push('0');
    } else {
        let mut temp = q;
        let mut temp_vec = Vec::<char>::new();
        while temp > 0 {
            if temp % 2 == 1 {
                temp_vec.push('1');
            } else {
                temp_vec.push('0');
            }
            temp = temp / 2;
        }
        for i in 0..temp_vec.len() {
            quotient.push(temp_vec[temp_vec.len() - 1 - i]);
        }
    }
    
    // Convert remainder to binary string
    if r == 0 {
        remainder.push('0');
    } else {
        let mut temp = r;
        let mut temp_vec = Vec::<char>::new();
        while temp > 0 {
            if temp % 2 == 1 {
                temp_vec.push('1');
            } else {
                temp_vec.push('0');
            }
            temp = temp / 2;
        }
        for i in 0..temp_vec.len() {
            remainder.push(temp_vec[temp_vec.len() - 1 - i]);
        }
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
{/* code modified by LLM (iteration 3): removed invalid int suffix from literals */
    if sy.len() == 0 || (sy.len() == 1 && sy[0] == '0') {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    if n == 0 {
        let mut result = Vec::<char>::new();
        for i in 0..sx.len() {
            result.push(sx[i]);
        }
        let (_, remainder) = DivMod(&result, sz);
        return remainder;
    }
    
    let mut sy_half = Vec::<char>::new();
    for i in 0..sy.len() - 1 {
        sy_half.push(sy[i]);
    }
    
    let half_result = ModExpPow2(sx, &sy_half, n - 1, sz);
    
    let mut temp = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i = half_result.len();
    
    while i > 0 || carry > 0 {
        let mut val = carry;
        if i > 0 {
            i = i - 1;
            val = val + if half_result[i] == '1' { 1 } else { 0 };
        }
        val = val * 2;
        
        if val >= 2 {
            temp.push('0');
            carry = 1;
        } else if val == 1 {
            temp.push('1');
            carry = 0;
        } else {
            temp.push('0');
            carry = 0;
        }
    }
    
    let mut squared = Vec::<char>::new();
    for i in 0..temp.len() {
        squared.push(temp[temp.len() - 1 - i]);
    }
    
    let (_, result) = DivMod(&squared, sz);
    result
}
// </vc-code>

fn main() {}
}


