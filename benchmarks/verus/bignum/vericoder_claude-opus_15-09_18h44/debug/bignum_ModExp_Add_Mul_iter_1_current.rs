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
{    let mut carry = 0u8;
    let mut result = Vec::<char>::new();
    let mut i = 0;
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant
            0 <= i <= s1.len() || i <= s2.len(),
            carry <= 1,
            ValidBitString(result@),
            Str2Int(result@) + carry as nat * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, i.min(s1.len()) as int)) + 
                Str2Int(s2@.subrange(0, i.min(s2.len()) as int)),
    {
        let bit1 = if i < s1.len() { 
            if s1[i] == '1' { 1u8 } else { 0u8 }
        } else { 
            0u8 
        };
        
        let bit2 = if i < s2.len() { 
            if s2[i] == '1' { 1u8 } else { 0u8 }
        } else { 
            0u8 
        };
        
        let sum = bit1 + bit2 + carry;
        carry = sum / 2;
        let bit = sum % 2;
        
        if bit == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        i = i + 1;
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
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i = 0;
    while i < s2.len()
        invariant
            0 <= i <= s2.len(),
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, i as int)),
    {
        let mut temp = result.clone();
        result = Add(&temp, &temp);
        
        if s2[s2.len() - 1 - i] == '1' {
            temp = result.clone();
            let mut shifted_s1 = s1.to_vec();
            let mut j = 0;
            while j < i
                invariant
                    0 <= j <= i,
                    ValidBitString(shifted_s1@),
                    Str2Int(shifted_s1@) == Str2Int(s1@) * Exp_int(2, j as nat),
            {
                shifted_s1.insert(0, '0');
                j = j + 1;
            }
            result = Add(&temp, &shifted_s1);
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
    
    let mut base = sx.to_vec();
    let mut exp = sy.to_vec();
    let mut result = Vec::<char>::new();
    result.push('1');
    
    let mut i = 0;
    while i < exp.len()
        invariant
            0 <= i <= exp.len(),
            ValidBitString(base@),
            ValidBitString(result@),
            ValidBitString(exp@),
            exp@.len() > 0,
            Str2Int(sz@) > 1,
    {
        if exp[i] == '1' {
            let temp = Mul(&result, &base);
            result = Mod(&temp, sz);
        }
        
        if i < exp.len() - 1 {
            let temp = Mul(&base, &base);
            base = Mod(&temp, sz);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


