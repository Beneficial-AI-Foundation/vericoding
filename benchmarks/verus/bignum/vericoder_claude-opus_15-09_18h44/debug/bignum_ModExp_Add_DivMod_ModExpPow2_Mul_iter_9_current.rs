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
{/* code modified by LLM (iteration 8): implement binary addition with carry */
    let mut carry = 0u8;
    let mut result = Vec::new();
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            0 <= i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            Str2Int(result@) + carry as nat * Exp_int(2, i as nat) == (Str2Int(s1@.subrange(0, i.min(s1.len()) as int)) + Str2Int(s2@.subrange(0, i.min(s2.len()) as int))),
    {
        let bit1 = if i < s1.len() { if s1[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let bit2 = if i < s2.len() { if s2[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let sum = bit1 + bit2 + carry;
        result.push(if sum & 1 == 1 { '1' } else { '0' });
        carry = sum >> 1;
        i = i + 1;
    }
    result
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
{/* code modified by LLM (iteration 8): implement division using repeated subtraction */
    let mut quotient = vec!['0'];
    let mut remainder = dividend.to_vec();
    
    // Helper function for comparing bit strings
    let geq = |a: &[char], b: &[char]| -> bool {
        if a.len() > b.len() { return true; }
        if a.len() < b.len() { return false; }
        let mut i = a.len();
        while i > 0 {
            i = i - 1;
            if a[i] == '1' && b[i] == '0' { return true; }
            if a[i] == '0' && b[i] == '1' { return false; }
        }
        true
    };
    
    // Helper for subtraction
    let sub = |a: &[char], b: &[char]| -> Vec<char> {
        let mut borrow = 0u8;
        let mut result = Vec::new();
        let mut i = 0;
        while i < a.len() {
            let bit_a = if a[i] == '1' { 1u8 } else { 0u8 };
            let bit_b = if i < b.len() { if b[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
            let diff = bit_a as i8 - bit_b as i8 - borrow as i8;
            if diff >= 0 {
                result.push(if diff == 1 { '1' } else { '0' });
                borrow = 0;
            } else {
                result.push('1');
                borrow = 1;
            }
            i = i + 1;
        }
        // Remove leading zeros
        while result.len() > 1 && result[result.len() - 1] == '0' {
            result.pop();
        }
        result
    };
    
    while geq(&remainder, divisor)
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
    {
        remainder = sub(&remainder, divisor);
        quotient = Add(&quotient, &vec!['1']);
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
{/* code modified by LLM (iteration 8): handle modular exponentiation for power of 2 - fix comparison type */
    if Str2Int(sy@) == 0nat {
        return vec!['1'];
    }
    
    // Compute y - 1 by subtracting 1 from the bit string
    let mut y_minus_one = sy.to_vec();
    let mut i = 0;
    let mut borrow = true;
    while i < y_minus_one.len() && borrow {
        if y_minus_one[i] == '1' {
            y_minus_one[i] = '0';
            borrow = false;
        } else {
            y_minus_one[i] = '1';
        }
        i = i + 1;
    }
    
    // Remove leading zeros if any
    while y_minus_one.len() > 1 && y_minus_one[y_minus_one.len() - 1] == '0' {
        y_minus_one.pop();
    }
    
    let ghost n_minus_1 = n - 1;
    let rec_result = ModExpPow2(sx, &y_minus_one, n_minus_1, sz);
    let squared = Mul(&rec_result, &rec_result);
    let (_, remainder) = DivMod(&squared, sz);
    remainder
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{/* code modified by LLM (iteration 8): implement binary multiplication using shift and add */
    let mut result = vec!['0'];
    let mut i = 0;
    while i < s2.len()
        invariant
            0 <= i <= s2.len(),
            ValidBitString(result@),
    {
        result = Add(&result, &result);
        if s2[s2.len() - 1 - i] == '1' {
            result = Add(&result, s1);
        }
        i = i + 1;
    }
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
{/* code modified by LLM (iteration 8): implement modular exponentiation using square and multiply */
    if sy.len() == 1 && sy[0] == '0' {
        return vec!['1'];
    }
    
    let last_bit = sy[sy.len() - 1];
    let y_div_2 = &sy[..sy.len() - 1];
    
    if y_div_2.len() == 0 || (y_div_2.len() == 1 && y_div_2[0] == '0') {
        // Base case: y = 1
        if last_bit == '1' {
            let (_, mod_x) = DivMod(sx, sz);
            return mod_x;
        } else {
            return vec!['1'];
        }
    }
    
    let half_exp = ModExp(sx, y_div_2, sz);
    let squared = Mul(&half_exp, &half_exp);
    let (_, mod_squared) = DivMod(&squared, sz);
    
    if last_bit == '1' {
        let mul_x = Mul(&mod_squared, sx);
        let (_, final_mod) = DivMod(&mul_x, sz);
        final_mod
    } else {
        mod_squared
    }
}
// </vc-code>

fn main() {}
}
