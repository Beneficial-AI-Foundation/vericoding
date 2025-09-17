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
/* helper modified by LLM (iteration 4): Fix compilation error by completing function signature with braces */
spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
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
/* code modified by LLM (iteration 4): Fix Add implementation with proper bitwise addition */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut res: Vec<char> = Vec::new();
    let mut carry = 0;
    
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i && i <= max_len,
            res@.len() == i,
            carry == 0 || carry == 1,
            Str2Int(res@) + carry * Exp_int(2, i as nat) == Str2Int(s1@.subrange(0, i)) + Str2Int(s2@.subrange(0, i))
        decreases max_len - i
    {
        let bit1_val = if i < len1 { if s1[i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2_val = if i < len2 { if s2[i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1_val + bit2_val + carry;
        carry = sum / 2;
        let bit_char = if sum % 2 == 1 { '1' } else { '0' };
        res.push(bit_char);
        i += 1;
    }
    
    if carry == 1 {
        res.push('1');
    }
    
    res
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix DivMod implementation with correct quotient/remainder calculation */
{
    let mut quotient: Vec<char> = Vec::new();
    let mut remainder: Vec<char> = dividend.to_vec();
    
    let divisor_val = Str2Int(divisor@) as int;
    let mut current_val = 0;
    let mut pos = 0;
    
    while pos < remainder.len()
        invariant
            0 <= pos && pos <= remainder.len(),
            current_val >= 0,
            current_val < divisor_val * Exp_int(2, (remainder.len() - pos) as nat) as int,
            Str2Int(quotient@) * divisor_val + current_val == Str2Int(dividend@.subrange(0, pos))
        decreases remainder.len() - pos
    {
        current_val = current_val * 2 + (if remainder[pos] == '1' { 1 } else { 0 });
        
        if current_val >= divisor_val {
            quotient.push('1');
            current_val -= divisor_val;
        } else if quotient.len() > 0 {
            quotient.push('0');
        }
        
        pos += 1;
    }
    
    if quotient.is_empty() {
        quotient.push('0');
    }
    
    let mut rem_vec = Vec::new();
    if current_val == 0 {
        rem_vec.push('0');
    } else {
        let mut temp = current_val;
        while temp > 0
            invariant
                temp >= 0
            decreases temp
        {
            if temp % 2 == 1 {
                rem_vec.push('1');
            } else {
                rem_vec.push('0');
            }
            temp /= 2;
        }
        rem_vec.reverse();
    }
    
    (quotient, rem_vec)
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
/* code modified by LLM (iteration 4): Fix ModExp implementation with correct modular exponentiation */
{
    let x_val = Str2Int(sx@) as int;
    let modulus_val = Str2Int(sz@) as int;
    let bit_length = sy.len();
    
    let mut result_vec = vec!['1'];
    let mut base = sx.to_vec();
    
    let mut i = bit_length;
    while i > 0
        invariant
            0 <= i && i <= bit_length,
            ValidBitString(result_vec@),
            ValidBitString(base@),
            Str2Int(result_vec@) as int == Exp_int(Str2Int(sx@), Str2Int(sy@.subrange(i, bit_length))) % modulus_val,
            Str2Int(base@) as int == Exp_int(Str2Int(sx@), Exp_int(2, (bit_length - i) as nat)) % modulus_val
        decreases i
    {
        i -= 1;
        
        let (_, sq_mod) = DivMod(&Mul(&result_vec, &result_vec), sz);
        
        if sy[i] == '1' {
            let (_, mul_mod) = DivMod(&Mul(&sq_mod, &base), sz);
            result_vec = mul_mod;
        } else {
            result_vec = sq_mod;
        }
        
        let (_, base_sq_mod) = DivMod(&Mul(&base, &base), sz);
        base = base_sq_mod;
    }
    
    result_vec
}
// </vc-code>

fn main() {}
}
