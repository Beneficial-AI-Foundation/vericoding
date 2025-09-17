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
    let mut carry = 0u8;
    let mut result = Vec::<char>::new();
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            0 <= i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            result.len() == i,
            Str2Int(result@) + carry as nat * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, if i as int <= s1@.len() { i as int } else { s1@.len() })) + 
                Str2Int(s2@.subrange(0, if i as int <= s2@.len() { i as int } else { s2@.len() }))
    {
        let bit1 = if i < s1.len() { if s1[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let bit2 = if i < s2.len() { if s2[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let sum = bit1 + bit2 + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i = i + 1;
    }
    
    while result.len() > 1 && result[result.len() - 1] == '0'
        invariant
            result.len() >= 1,
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@)
    {
        result.pop();
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
        remainder.push(dividend[dividend.len() - 1 - i]);
    }
    
    while remainder.len() > 0 && Str2Int(remainder@) >= Str2Int(divisor@)
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(remainder@) < Str2Int(divisor@) * Exp_int(2, 1),
            Str2Int(dividend@) == Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(remainder@)
    {
        let mut count = 0u8;
        let mut temp = remainder.clone();
        
        while Str2Int(temp@) >= Str2Int(divisor@)
            invariant
                ValidBitString(temp@),
                count <= 1,
                Str2Int(remainder@) == count as nat * Str2Int(divisor@) + Str2Int(temp@)
        {
            temp = Sub(&temp, divisor);
            count = count + 1;
        }
        
        quotient.push(if count == 1 { '1' } else { '0' });
        remainder = temp;
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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@.subrange(0, i as int)) * Str2Int(s2@)
    {
        if s1[i] == '1' {
            result = Add(&result, s2);
        }
        if i + 1 < s1.len() {
            result = Add(&result, &result);
        }
        i = i + 1;
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
    if sy.len() == 0 || (sy.len() == 1 && sy[0] == '0') {
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
    
    while exp.len() > 0 && !(exp.len() == 1 && exp[0] == '0')
        invariant
            ValidBitString(base@),
            ValidBitString(exp@),
            ValidBitString(result@),
            Str2Int(result@) * Exp_int(Str2Int(base@), Str2Int(exp@)) % Str2Int(sz@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
        decreases exp@.len()
    {
        if exp[0] == '1' {
            let temp = Mul(&result, &base);
            let (_, rem) = DivMod(&temp, sz);
            result = rem;
        }
        
        if !(exp.len() == 1 && exp[0] == '1') {
            let temp = Mul(&base, &base);
            let (_, rem) = DivMod(&temp, sz);
            base = rem;
        }
        
        let (quot, _) = DivMod(&exp, &vec!['0', '1']);
        exp = quot;
    }
    
    result
}
// </vc-code>

fn main() {}
}
