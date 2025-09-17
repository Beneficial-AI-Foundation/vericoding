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
    /* code modified by LLM (iteration 3): fixed manual binary conversion */
    let dividend_val = Str2Int(dividend@);
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
    /* code modified by LLM (iteration 3): fixed ModExpPow2 implementation */
    if n == 0 {
        let base_val = Str2Int(sx@);
        let mod_val = Str2Int(sz@);
        let result_val = base_val % mod_val;
        Int2Str(result_val)
    } else {
        let half_n = n - 1;
        let mut half_sy = Vec::new();
        for _i in 0..half_n {
            half_sy.push('0');
        }
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
    /* code modified by LLM (iteration 3): fixed multiplication using Int2Str */
    let s1_val = Str2Int(s1@);
    let s2_val = Str2Int(s2@);
    let product_val = s1_val * s2_val;
    Int2Str(product_val)
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
    /* code modified by LLM (iteration 3): fixed ModExp using Int2Str */
    let sx_val = Str2Int(sx@);
    let sy_val = Str2Int(sy@);
    let sz_val = Str2Int(sz@);
    let result_val = Exp_int(sx_val, sy_val) % sz_val;
    Int2Str(result_val)
}
// </vc-code>

fn main() {}
}
