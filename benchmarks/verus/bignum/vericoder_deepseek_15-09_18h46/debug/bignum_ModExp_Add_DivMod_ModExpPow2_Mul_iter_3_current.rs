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
/* code modified by LLM (iteration 3): Added max helper function */
fn max(a: usize, b: usize) -> usize { if a > b { a } else { b } }
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed Add implementation with proper max helper */
{
    let mut res = Vec::empty();
    let mut carry = 0;
    let s1_len = s1.len();
    let s2_len = s2.len();
    let max_len = max(s1_len, s2_len);
    
    for i in 0..max_len {
        let bit1 = if i < s1_len && s1[i] == '1' { 1 } else { 0 };
        let bit2 = if i < s2_len && s2[i] == '1' { 1 } else { 0 };
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
/* code modified by LLM (iteration 3): Fixed DivMod implementation with proper binary division */
{
    let mut quotient = Vec::empty();
    let mut remainder = Vec::empty();
    
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
        let rem_str = remainder.iter().collect::<String>();
        let rem_seq = Seq::from_str(&rem_str);
        if Str2Int(rem_seq) >= Str2Int(divisor@) {
            quotient.push('1');
            let rem_val = Str2Int(rem_seq);
            let div_val = Str2Int(divisor@);
            let new_remainder_val = rem_val - div_val;
            remainder = new_remainder_val.to_bin_vec();
        } else {
            quotient.push('0');
        }
    }
    
    (quotient, remainder)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed ModExpPow2 implementation with proper binary operations */
{
    if n == 0 {
        let sx_val = Str2Int(sx@);
        let sy_val = Str2Int(sy@);
        let sz_val = Str2Int(sz@);
        let exp_result = if sy_val == 0 { 1 } else { sx_val };
        return (exp_result % sz_val).to_bin_vec();
    } else {
        let half_n = n - 1;
        let mut sy_half = Vec::new();
        for i in 0..sy.len() - 1 {
            sy_half.push(sy[i]);
        }
        let result_half = ModExpPow2(sx, &sy_half, half_n, sz);
        let square = Mul(&result_half, &result_half);
        
        if sy[sy.len() - 1] == '1' {
            let product = Mul(&square, sx);
            let sz_val = Str2Int(sz@);
            (Str2Int(product@) % sz_val).to_bin_vec()
        } else {
            let sz_val = Str2Int(sz@);
            (Str2Int(square@) % sz_val).to_bin_vec()
        }
    }
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
/* code modified by LLM (iteration 3): Fixed Mul implementation with shift operations */
{
    let mut result = Vec::empty();
    result.push('0');
    
    for i in 0..s2.len() {
        if s2[i] == '1' {
            let mut shifted_s1 = s1.to_vec();
            for _ in 0..i {
                shifted_s1.push('0');
            }
            result = Add(&result, &shifted_s1);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}
