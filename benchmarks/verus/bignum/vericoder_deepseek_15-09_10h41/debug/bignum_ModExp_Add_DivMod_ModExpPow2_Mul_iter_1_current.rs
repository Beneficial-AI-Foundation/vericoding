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
    let mut i = s1.len();
    let mut j = s2.len();
    let mut carry = false;
    let mut result = Vec::new();
    let mut a: bool;
    let mut b: bool;
    let mut sum: u8;
    
    while i > 0 || j > 0 || carry
        invariant
            0 <= i && i <= s1.len(),
            0 <= j && j <= s2.len(),
            result@.len() == (s1.len() - i) + (s2.len() - j) + (if carry { 1 } else { 0 }),
            ValidBitString(result@),
            Str2Int(result@) + Exp_int(2, result@.len() as nat) * (if carry { 1 } else { 0 }) == Str2Int(s1.subrange(i as int, s1.len() as int)) + Str2Int(s2.subrange(j as int, s2.len() as int))
        decreases i + j
    {
        a = if i > 0 { s1[i - 1] == '1' } else { false };
        b = if j > 0 { s2[j - 1] == '1' } else { false };
        
        sum = (if a { 1 } else { 0 }) + (if b { 1 } else { 0 }) + (if carry { 1 } else { 0 });
        
        if sum & 1 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        carry = sum >= 2;
        
        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
    }
    
    result.reverse();
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
{
    let mut dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);
    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;
    
    let quotient_str = Int2Str(quotient_val);
    let remainder_str = Int2Str(remainder_val);
    
    (quotient_str, remainder_str)
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
        let mut result = Vec::new();
        if Str2Int(sx@) % Str2Int(sz@) == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        result
    } else {
        let half_n = n - 1;
        let half_sy = Vec::from_iter(std::iter::repeat('0').take(half_n as usize));
        half_sy.push('1');
        
        let half_result = ModExpPow2(sx, &half_sy, half_n, sz);
        let squared = Mul(&half_result, &half_result);
        let mod_result = DivMod(&squared, sz).1;
        
        if sy[sy.len() - 1] == '1' {
            let temp = Mul(&mod_result, sx);
            DivMod(&temp, sz).1
        } else {
            mod_result
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
    let mut result = Vec::new();
    result.push('0');
    
    let mut temp_s2 = s2.to_vec();
    
    while !temp_s2.is_empty()
        invariant
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(Vec::from_slice(temp_s2.as_slice())@)
        decreases temp_s2.len()
    {
        if temp_s2[temp_s2.len() - 1] == '1' {
            let sum = Add(&result, s1);
            result = sum;
        }
        
        result.push('0');
        temp_s2.pop();
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
    if sy.len() == 1 {
        if sy[0] == '0' {
            let mut result = Vec::new();
            result.push('1');
            result
        } else {
            DivMod(sx, sz).1
        }
    } else {
        let half_sy = &sy[0..sy.len() - 1];
        let half_exp = ModExp(sx, half_sy, sz);
        let squared = Mul(&half_exp, &half_exp);
        let mod_squared = DivMod(&squared, sz).1;
        
        if sy[sy.len() - 1] == '1' {
            let temp = Mul(&mod_squared, sx);
            DivMod(&temp, sz).1
        } else {
            mod_squared
        }
    }
}
// </vc-code>

fn main() {}
}
