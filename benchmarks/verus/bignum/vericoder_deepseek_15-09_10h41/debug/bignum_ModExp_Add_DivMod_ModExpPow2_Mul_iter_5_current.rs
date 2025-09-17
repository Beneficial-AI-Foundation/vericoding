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
fn Int2Str(n: nat) -> Vec<char> 
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        vec!['0']
    } else if n == 1 {
        vec!['1']
    } else {
        let mut result = Int2Str(n / 2);
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        result
    }
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
    /* code modified by LLM (iteration 5): manual binary division algorithm */
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
        if Str2Int(remainder@) >= Str2Int(divisor@) {
            quotient.push('1');
            let rem_val = Str2Int(remainder@) - Str2Int(divisor@);
            remainder = Int2Str(rem_val);
        } else {
            quotient.push('0');
        }
    }
    
    // Remove leading zeros from quotient
    while quotient.len() > 1 && quotient[0] == '0' {
        quotient.remove(0);
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
    /* code modified by LLM (iteration 5): fixed ModExpPow2 recursive implementation */
    if n == 0 {
        let base_val = Str2Int(sx@);
        let mod_val = Str2Int(sz@);
        let result_val = base_val % mod_val;
        Int2Str(result_val)
    } else {
        let half_n = n - 1;
        let mut half_sy = Vec::new();
        for i in 0..n {
            if i == half_n {
                half_sy.push('1');
            } else {
                half_sy.push('0');
            }
        }
        
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
    /* code modified by LLM (iteration 5): manual binary multiplication algorithm */
    let mut result = vec!['0'];
    let s1_val = Str2Int(s1@);
    let s2_val = Str2Int(s2@);
    
    for i in 0..s2_val {
        result = Add(&result, s1).0;
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
    /* code modified by LLM (iteration 5): efficient modular exponentiation */
    let base_val = Str2Int(sx@);
    let exp_val = Str2Int(sy@);
    let mod_val = Str2Int(sz@);
    
    if exp_val == 0 {
        Int2Str(1 % mod_val)
    } else {
        let mut result = vec!['1'];
        let mut base = Int2Str(base_val % mod_val);
        let mut exp = sy.to_vec();
        
        while !exp.is_empty() {
            if exp.last() == Some(&'1') {
                let temp = Mul(&result, &base);
                result = DivMod(&temp, sz).1;
            }
            
            // Square the base
            let temp = Mul(&base, &base);
            base = DivMod(&temp, sz).1;
            
            // Right shift exponent
            exp.pop();
        }
        
        result
    }
}
// </vc-code>

fn main() {}
}
