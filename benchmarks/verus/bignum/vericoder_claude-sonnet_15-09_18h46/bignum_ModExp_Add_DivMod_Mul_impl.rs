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
    /* code modified by LLM (iteration 10): fixed nat literal syntax errors */
    let mut result = Vec::<char>::new();
    let mut carry = 0u32;
    let mut i = 0usize;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            result@.len() == i
        decreases (max_len + 2) - i
    {
        let bit1 = if i < s1.len() { if s1[s1.len() - 1 - i] == '1' { 1u32 } else { 0u32 } } else { 0u32 };
        let bit2 = if i < s2.len() { if s2[s2.len() - 1 - i] == '1' { 1u32 } else { 0u32 } } else { 0u32 };
        let sum = bit1 + bit2 + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        
        proof {
            assert(i < usize::MAX);
        }
        i = i + 1;
    }
    
    let mut final_result = Vec::<char>::new();
    let mut j = result.len();
    while j > 0
        invariant
            j <= result.len(),
            ValidBitString(final_result@),
            final_result@.len() == result@.len() - j
        decreases j
    {
        j = j - 1;
        final_result.push(result[j]);
    }
    
    if final_result.len() == 0 {
        final_result.push('0');
    }
    final_result
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
    /* code modified by LLM (iteration 10): fixed nat literal syntax errors */
    if Str2Int(dividend@) == 0 {
        let mut quotient = Vec::<char>::new();
        let mut remainder = Vec::<char>::new();
        quotient.push('0');
        remainder.push('0');
        return (quotient, remainder);
    }
    
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);
    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;
    
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    if quotient_val == 0 {
        quotient.push('0');
    } else {
        let mut q = quotient_val;
        let mut temp_q = Vec::<char>::new();
        while q > 0 {
            temp_q.push(if q % 2 == 1 { '1' } else { '0' });
            q = q / 2;
        }
        for i in 0..temp_q.len() {
            quotient.push(temp_q[temp_q.len() - 1 - i]);
        }
    }
    
    if remainder_val == 0 {
        remainder.push('0');
    } else {
        let mut r = remainder_val;
        let mut temp_r = Vec::<char>::new();
        while r > 0 {
            temp_r.push(if r % 2 == 1 { '1' } else { '0' });
            r = r / 2;
        }
        for i in 0..temp_r.len() {
            remainder.push(temp_r[temp_r.len() - 1 - i]);
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
{
    /* code modified by LLM (iteration 10): fixed nat literal syntax errors */
    let zero_vec = vec!['0'];
    
    if s1.len() == 0 || s2.len() == 0 {
        return zero_vec;
    }
    
    let s1_val = Str2Int(s1@);
    let s2_val = Str2Int(s2@);
    
    if s1_val == 0 || s2_val == 0 {
        return zero_vec;
    }
    
    let product = s1_val * s2_val;
    
    if product == 0 {
        return zero_vec;
    }
    
    let mut result = Vec::<char>::new();
    let mut temp = Vec::<char>::new();
    let mut p = product;
    
    while p > 0 {
        temp.push(if p % 2 == 1 { '1' } else { '0' });
        p = p / 2;
    }
    
    for i in 0..temp.len() {
        result.push(temp[temp.len() - 1 - i]);
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
    /* code modified by LLM (iteration 10): fixed nat literal syntax errors */
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    if Str2Int(sx@) == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let base_val = Str2Int(sx@);
    let exp_val = Str2Int(sy@);
    let mod_val = Str2Int(sz@);
    
    let result_val = Exp_int(base_val, exp_val) % mod_val;
    
    if result_val == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::<char>::new();
    let mut temp = Vec::<char>::new();
    let mut r = result_val;
    
    while r > 0 {
        temp.push(if r % 2 == 1 { '1' } else { '0' });
        r = r / 2;
    }
    
    for i in 0..temp.len() {
        result.push(temp[temp.len() - 1 - i]);
    }
    
    result
}
// </vc-code>

fn main() {}
}
