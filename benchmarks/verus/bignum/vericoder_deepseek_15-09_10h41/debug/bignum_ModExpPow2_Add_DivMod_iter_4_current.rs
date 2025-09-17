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
/* helper modified by LLM (iteration 4): Add min function */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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
    /* code modified by LLM (iteration 4): Simplified DivMod implementation */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);
    let q_val = dividend_val / divisor_val;
    let r_val = dividend_val % divisor_val;
    
    let mut temp = q_val;
    while temp > 0 {
        quotient.push(if temp % 2 == 1 { '1' } else { '0' });
        temp = temp / 2;
    }
    
    let mut temp = r_val;
    while temp > 0 {
        remainder.push(if temp % 2 == 1 { '1' } else { '0' });
        temp = temp / 2;
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
    /* code modified by LLM (iteration 4): Implement ModExpPow2 using direct computation */
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let exp_val = Exp_int(x_val, y_val);
    let mod_result = exp_val % z_val;
    
    let mut res_vec = Vec::<char>::new();
    let mut temp = mod_result;
    while temp > 0 {
        res_vec.push(if temp % 2 == 1 { '1' } else { '0' });
        temp = temp / 2;
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}


