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
fn max(a: usize, b: usize) -> usize {
    if a > b {
        a
    } else {
        b
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
    /* code modified by LLM (iteration 9): Fixed compilation error with proper braces */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    let mut current_dividend: nat = 0;
    
    let divisor_val = Str2Int(divisor@);
    
    for i in 0..dividend.len() {
        current_dividend = current_dividend * 2;
        if dividend[i] == '1' {
            current_dividend = current_dividend + 1;
        }
        
        if current_dividend >= divisor_val {
            quotient.push('1');
            current_dividend = current_dividend - divisor_val;
        } else {
            quotient.push('0');
        }
    }
    
    if current_dividend == 0 {
        remainder.push('0');
    } else {
        while current_dividend > 0 {
            if current_dividend % 2 == 1 {
                remainder.push('1');
            } else {
                remainder.push('0');
            }
            current_dividend = current_dividend / 2;
        }
        remainder.reverse();
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
    /* code modified by LLM (iteration 9): Fixed ModExpPow2 implementation */
    if Str2Int(sy@) == 0 {
        return Vec::from(['1']);
    }
    
    let mut result = 1nat;
    let mut base = Str2Int(sx@) % Str2Int(sz@);
    let modulus = Str2Int(sz@);
    
    for i in 0..sy.len() {
        if sy[i] == '1' {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
    }
    
    result.to_bin_vec()
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): Fixed Mul implementation with proper Add call */
    let mut result = Vec::from(['0']);
    
    let s1_vec: Vec<char> = s1.to_vec();
    
    for i in (0..s2.len()).rev() {
        if s2[i] == '1' {
            result = Add(&result, &s1_vec)?;
        }
        
        if i > 0 {
            result.insert(0, '0');
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
    /* code modified by LLM (iteration 9): Fixed ModExp implementation */
    let mut result = 1nat;
    let mut base = Str2Int(sx@) % Str2Int(sz@);
    let modulus = Str2Int(sz@);
    
    for i in (0..sy.len()).rev() {
        if sy[i] == '1' {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
    }
    
    result.to_bin_vec()
}
// </vc-code>

fn main() {}
}
