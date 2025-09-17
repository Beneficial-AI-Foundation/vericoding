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
/* helper modified by LLM (iteration 3): Fix Str2Int to use slicing syntax instead of subrange */
spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
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
/* code modified by LLM (iteration 3): Fix subrange usage, type comparisons, and arithmetic operations */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut res = Vec::<char>::new();
    let mut carry = 0;
    
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i && i <= max_len,
            ValidBitString(res@),
            Str2Int(res@) + carry * Exp_int(2, i) == 
                Str2Int(s1@.subrange(0, i)) + Str2Int(s2@.subrange(0, i))
        decreases max_len - i
    {
        let bit1 = if i < len1 { if s1[i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < len2 { if s2[i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        carry = if sum >= 2 { 1 } else { 0 };
        let res_bit = if sum % 2 == 1 { '1' } else { '0' };
        res.push(res_bit);
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
/* code modified by LLM (iteration 3): Fix subrange usage and nat/int operations */
{
    let mut quotient = Vec::<char>::new();
    let mut remainder = dividend.to_vec();
    
    let divisor_val = Str2Int(divisor@);
    
    let mut pos = 0;
    let mut current_val = 0;
    
    while pos < remainder.len()
        invariant
            0 <= pos && pos <= remainder.len(),
            ValidBitString(remainder@),
            current_val >= 0,
            Str2Int(quotient@) * divisor_val + current_val == Str2Int(dividend@.subrange(0, pos))
        decreases remainder.len() - pos
    {
        current_val = current_val * 2 + (if remainder[pos] == '1' { 1 } else { 0 });
        
        if current_val >= divisor_val as int {
            quotient.push('1');
            current_val -= divisor_val as int;
        } else if quotient.len() > 0 {
            quotient.push('0');
        }
        
        pos += 1;
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    let mut rem_str = Vec::<char>::new();
    if current_val == 0 {
        rem_str.push('0');
    } else {
        let mut temp = current_val;
        while temp > 0
            invariant
                temp >= 0
            decreases temp
        {
            if temp % 2 == 1 {
                rem_str.insert(0, '1');
            } else {
                rem_str.insert(0, '0');
            }
            temp /= 2;
        }
    }
    
    (quotient, rem_str)
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
/* code modified by LLM (iteration 3): Fix subrange usage and verification issues */
{
    let x = Str2Int(sx@) as int;
    let modulus = Str2Int(sz@) as int;
    let bit_length = sy.len();
    
    let mut result = vec!['1'];
    let mut base = sx.to_vec();
    
    let mut i = bit_length;
    while i > 0
        invariant
            0 <= i && i <= bit_length,
            ValidBitString(result@),
            ValidBitString(base@),
            Str2Int(result@) as int == Exp_int(Str2Int(sx@), Str2Int(sy@.subrange(i, bit_length))) % modulus,
            Str2Int(base@) as int == Exp_int(Str2Int(sx@), Exp_int(2, bit_length - i)) % modulus
        decreases i
    {
        i -= 1;
        proof {
            assert(Str2Int(sy@.subrange(i, bit_length)) == Str2Int(sy@.subrange(i, i+1)) + 2 * Str2Int(sy@.subrange(i+1, bit_length)));
        }
        
        let squared = Mul(&result, &result);
        let (_, squared_mod) = DivMod(&squared, sz);
        
        if sy[i] == '1' {
            let multiplied = Mul(&squared_mod, &base);
            let (_, multiplied_mod) = DivMod(&multiplied, sz);
            result = multiplied_mod;
        } else {
            result = squared_mod;
        }
        
        let base_squared = Mul(&base, &base);
        let (_, base_squared_mod) = DivMod(&base_squared, sz);
        base = base_squared_mod;
    }
    
    result
}
// </vc-code>

fn main() {}
}
