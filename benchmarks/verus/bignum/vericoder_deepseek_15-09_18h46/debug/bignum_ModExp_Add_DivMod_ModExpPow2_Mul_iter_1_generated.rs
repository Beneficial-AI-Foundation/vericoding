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
    let mut res = Vec::empty();
    let mut carry = 0;
    let max_len = max(s1.len(), s2.len()) as int;
    
    for i in 0..max_len {
        let bit1 = if i < s1.len() as int && s1[i as usize] == '1' { 1 } else { 0 };
        let bit2 = if i < s2.len() as int && s2[i as usize] == '1' { 1 } else { 0 };
        let sum = bit1 + bit2 + carry;
        res.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
    }
    
    if carry > 0 {
        res.push('1');
    }
    
    res.reverse();
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
    let mut quotient = Vec::empty();
    let mut remainder = Vec::empty();
    let divisor_val = Str2Int(divisor@);
    
    for i in 0..dividend.len() as int {
        remainder.push(dividend[i as usize]);
        if Str2Int(remainder@) >= divisor_val {
            let rem_val = Str2Int(remainder@);
            quotient.push('1');
            let new_remainder_val = rem_val - divisor_val;
            remainder = (new_remainder_val as u64).to_bin_vec();
        } else {
            quotient.push('0');
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
{
    if n == 0 {
        let sx_val = Str2Int(sx@);
        let sy_val = Str2Int(sy@);
        let exp_result = if sy_val == 0 { 1 } else { sx_val };
        return (exp_result % Str2Int(sz@) as u64).to_bin_vec();
    } else {
        let half_n = n - 1;
        let mut sy_half = sy.subrange(0, sy.len() as int - 1);
        let result_half = ModExpPow2(&sx.to_vec(), &sy_half.to_vec(), half_n, sz);
        let square = Mul(&result_half, &result_half);
        
        if sy[sy.len() - 1] == '1' {
            let product = Mul(&square, sx);
            Mod(&product, sz)
        } else {
            Mod(&square, sz)
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
{
    let mut result = Vec::empty();
    result.push('0');
    let s1_val = Str2Int(s1@);
    let s2_val = Str2Int(s2@);
    
    for i in 0..s2.len() as int {
        if s2[i as usize] == '1' {
            let shifted_s1 = s1.shift_left(i);
            result = Add(&result, &shifted_s1);
        }
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
{
    if sy.len() == 0 {
        return (1 as u64).to_bin_vec();
    }
    
    let last_char = sy[sy.len() - 1];
    let mut sy_prefix = sy.subrange(0, sy.len() as int - 1).to_vec();
    
    let prefix_result = ModExp(sx, &sy_prefix, sz);
    let squared = Mul(&prefix_result, &prefix_result);
    let mod_squared = Mod(&squared, sz);
    
    if last_char == '1' {
        let multiplied = Mul(&mod_squared, sx);
        Mod(&multiplied, sz)
    } else {
        mod_squared
    }
}
// </vc-code>

fn main() {}
}
