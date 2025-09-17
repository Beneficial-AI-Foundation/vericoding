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
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    
    while i <= max_len
        invariant
            i <= max_len + 1,
            ValidBitString(result@),
            carry <= 1
    {
        let bit1 = if i < len1 { if s1[len1 - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < len2 { if s2[len2 - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        result.push(result_bit);
        carry = sum / 2;
        if carry == 0 && i >= max_len { break; }
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
    
    let mut i = 0;
    while i < s2.len()
        invariant
            i <= s2.len(),
            ValidBitString(result@)
    {
        if s2[s2.len() - 1 - i] == '1' {
            let mut shifted = Vec::<char>::new();
            let mut j = 0;
            while j < i {
                shifted.push('0');
                j += 1;
            }
            for k in 0..s1.len() {
                shifted.push(s1[k]);
            }
            result = Add(&result, &shifted);
        }
        i += 1;
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
    if sy.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let mut base = sx.to_vec();
    let mut exp = sy.to_vec();
    let modulus = sz;
    let mut result = Vec::<char>::new();
    result.push('1');
    
    while exp.len() > 0 && !(exp.len() == 1 && exp[0] == '0')
        invariant
            ValidBitString(base@),
            ValidBitString(exp@),
            ValidBitString(result@)
        decreases exp@.len()
    {
        if exp[exp.len() - 1] == '1' {
            let temp = Mul(&result, &base);
            result = ModExp(&temp, &vec!['1'], modulus);
        }
        
        let temp_base = Mul(&base, &base);
        base = ModExp(&temp_base, &vec!['1'], modulus);
        
        let mut new_exp = Vec::<char>::new();
        let mut carry = 0;
        let mut i = 0;
        while i < exp.len() {
            let digit = if exp[i] == '1' { 1 } else { 0 };
            let new_digit = (digit + carry * 2) / 2;
            carry = (digit + carry * 2) % 2;
            if i < exp.len() - 1 {
                new_exp.push(if new_digit == 1 { '1' } else { '0' });
            }
            i += 1;
        }
        exp = new_exp;
        if exp.len() == 0 {
            break;
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


