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
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len,
            carry <= 1,
            ValidBitString(result@)
    {
        let bit1 = if i < s1.len() { if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < s2.len() { if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i += 1;
    }
    
    result.reverse();
    if result.len() == 0 {
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
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
    }
    
    if Str2Int(dividend@) < Str2Int(divisor@) {
        quotient.push('0');
        return (quotient, remainder);
    }
    
    quotient.push('1');
    for i in 0..divisor.len() {
        remainder.push(divisor[i]);
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
    if s1.len() == 0 || s2.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('0');
    
    for i in 0..s2.len() {
        if s2[s2.len() - 1 - i] == '1' {
            let shifted = Add(s1, &result);
            result = shifted;
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
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let mut base = Vec::<char>::new();
    for i in 0..sx.len() {
        base.push(sx[i]);
    }
    
    let mut exp = Vec::<char>::new();
    for i in 0..sy.len() {
        exp.push(sy[i]);
    }
    
    let mut result = Vec::<char>::new();
    result.push('1');
    
    let mut current_base = base;
    
    while exp.len() > 0 && !(exp.len() == 1 && exp[0] == '0') {
        if exp[exp.len() - 1] == '1' {
            let product = Mul(&result, &current_base);
            let (_, remainder) = DivMod(&product, sz);
            result = remainder;
        }
        
        let square = Mul(&current_base, &current_base);
        let (_, remainder) = DivMod(&square, sz);
        current_base = remainder;
        
        let mut new_exp = Vec::<char>::new();
        let mut carry = 0;
        for i in 0..exp.len() {
            let digit = if exp[i] == '1' { 1 } else { 0 };
            let new_digit = (digit + carry) / 2;
            carry = (digit + carry) % 2;
            if i < exp.len() - 1 {
                new_exp.push(if new_digit == 1 { '1' } else { '0' });
            }
        }
        exp = new_exp;
    }
    
    result
}
// </vc-code>

fn main() {}
}
