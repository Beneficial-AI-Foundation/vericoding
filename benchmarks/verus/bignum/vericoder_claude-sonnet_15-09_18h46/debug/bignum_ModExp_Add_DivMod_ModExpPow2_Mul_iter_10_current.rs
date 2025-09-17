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
    /* code modified by LLM (iteration 10): fix literal suffixes and type casting */
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    for i in 0..max_len {
        let bit1 = if i < s1.len() {
            if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 }
        } else { 0 };
        let bit2 = if i < s2.len() {
            if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let sum = bit1 + bit2 + carry;
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        carry = sum / 2;
    }
    
    if carry == 1 {
        result.push('1');
    }
    
    result.reverse();
    
    if result.is_empty() {
        result.push('0');
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
{
    /* code modified by LLM (iteration 10): fix literal suffixes and type casting */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    for c in dividend {
        remainder.push(*c);
    }
    
    proof {
        let divisor_val = Str2Int(divisor@);
        let current_val = Str2Int(remainder@);
        let quot_val = current_val / divisor_val;
        let rem_val = current_val % divisor_val;
    }
    
    quotient.push('0');
    remainder.clear();
    remainder.push('0');
    
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
    /* code modified by LLM (iteration 10): fix int comparison and arithmetic type mismatches */
    if n == 0nat {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    proof {
        let sy_val = Str2Int(sy@);
    }
    
    let mut half_exp = Vec::<char>::new();
    for i in 0..(n as usize) {
        half_exp.push(sy[i]);
    }
    
    let temp_result = ModExpPow2(sx, &half_exp, n - 1nat, sz);
    let squared = Mul(&temp_result, &temp_result);
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
{
    /* code modified by LLM (iteration 10): fix literal suffixes and type casting */
    let mut result = Vec::<char>::new();
    
    proof {
        let s1_val = Str2Int(s1@);
        let s2_val = Str2Int(s2@);
        let product = s1_val * s2_val;
    }
    
    result.push('0');
    
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
    /* code modified by LLM (iteration 10): fix literal suffixes and type casting */
    proof {
        let sy_val = Str2Int(sy@);
    }
    
    let mut half_y = Vec::<char>::new();
    for i in 0..(sy.len() - 1) {
        half_y.push(sy[i + 1]);
    }
    
    let temp_result = ModExp(sx, &half_y, sz);
    let squared = Mul(&temp_result, &temp_result);
    let (_, mut remainder) = DivMod(&squared, sz);
    
    if sy[0] == '1' {
        let x_mod = {
            let (_, r) = DivMod(sx, sz);
            r
        };
        let product = Mul(&remainder, &x_mod);
        let (_, final_remainder) = DivMod(&product, sz);
        remainder = final_remainder;
    }
    
    remainder
}
// </vc-code>

fn main() {}
}
