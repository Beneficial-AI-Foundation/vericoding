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
    /* code modified by LLM (iteration 5): added decreases clause for binary addition loop */
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i = s1.len();
    let mut j = s2.len();
    
    while i > 0 || j > 0 || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 1,
            i <= s1.len(),
            j <= s2.len()
        decreases i + j + carry
    {
        let bit1 = if i > 0 { if s1[i - 1] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if j > 0 { if s2[j - 1] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        
        if sum % 2 == 1 {
            result.insert(0, '1');
        } else {
            result.insert(0, '0');
        }
        
        carry = sum / 2;
        
        if i > 0 { i = i - 1; }
        if j > 0 { j = j - 1; }
    }
    
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
    /* code modified by LLM (iteration 5): division with simplified approach */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    for bit in dividend.iter()
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@)
    {
        remainder.push(*bit);
        
        let mut is_greater_equal = false;
        if remainder.len() > divisor.len() {
            is_greater_equal = true;
        } else if remainder.len() == divisor.len() {
            let mut i = 0;
            let mut equal = true;
            while i < remainder.len() && equal {
                if remainder[i] > divisor[i] {
                    is_greater_equal = true;
                    equal = false;
                } else if remainder[i] < divisor[i] {
                    equal = false;
                }
                i = i + 1;
            }
            if equal {
                is_greater_equal = true;
            }
        }
        
        if is_greater_equal {
            quotient.push('1');
            remainder = Vec::<char>::new();
            remainder.push('0');
        } else {
            quotient.push('0');
        }
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    if remainder.len() == 0 {
        remainder.push('0');
    }
    
    (quotient, remainder)
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
    /* code modified by LLM (iteration 5): basic modular exponentiation */
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    if sx.len() == 1 && sx[0] == '0' {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('1');
    
    let mut base = Vec::<char>::new();
    for c in sx.iter() {
        base.push(*c);
    }
    
    let mut exp = Vec::<char>::new();
    for c in sy.iter() {
        exp.push(*c);
    }
    
    while exp.len() > 0 && !(exp.len() == 1 && exp[0] == '0')
        invariant
            ValidBitString(base@),
            ValidBitString(exp@),
            ValidBitString(result@)
        decreases
            exp.len()
    {
        result = Add(&result, &base);
        
        if exp.len() > 1 {
            exp.pop();
        } else {
            exp[0] = '0';
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


