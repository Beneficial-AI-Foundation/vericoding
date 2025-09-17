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
    /* code modified by LLM (iteration 8): ensure correct type usage throughout */
    let mut carry = 0u8;
    let mut result = Vec::new();
    let n1 = s1.len();
    let n2 = s2.len();
    let max_len = if n1 > n2 { n1 } else { n2 };
    
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            0 <= i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            result.len() == i,
            Str2Int(result@) + carry as nat * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, if i <= n1 { i as int } else { n1 as int })) + 
                Str2Int(s2@.subrange(0, if i <= n2 { i as int } else { n2 as int }))
    {
        let bit1 = if i < n1 { if s1[n1 - 1 - i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let bit2 = if i < n2 { if s2[n2 - 1 - i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let sum = bit1 + bit2 + carry;
        
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i = i + 1;
    }
    
    let mut reversed = Vec::new();
    let mut j = result.len();
    while j > 0
        invariant
            0 <= j <= result.len(),
            ValidBitString(reversed@),
            reversed.len() == result.len() - j,
            forall |k: int| 0 <= k && k < reversed.len() as int ==> 
                reversed@[k] == result@[result.len() as int - 1 - k]
    {
        j = j - 1;
        reversed.push(result[j]);
    }
    
    reversed
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
    /* code modified by LLM (iteration 8): fix nat type comparisons */
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    let mut i = 0;
    while i < dividend.len()
        invariant
            0 <= i <= dividend.len(),
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(remainder@) < Str2Int(divisor@),
            i > 0 ==> Str2Int(dividend@.subrange(0, i as int)) == 
                Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(remainder@)
    {
        remainder.push(dividend[i]);
        
        if Str2Int(remainder@) >= Str2Int(divisor@) {
            quotient.push('1');
            let mut new_rem = Vec::new();
            let mut temp: nat = Str2Int(remainder@) - Str2Int(divisor@);
            
            while temp > 0nat
                invariant
                    ValidBitString(new_rem@),
                    Str2Int(new_rem@) + temp * Exp_int(2, new_rem.len() as nat) == 
                        Str2Int(remainder@) - Str2Int(divisor@)
            {
                new_rem.push(if temp % 2nat == 1nat { '1' } else { '0' });
                temp = temp / 2nat;
            }
            
            remainder = new_rem;
        } else {
            if quotient.len() > 0 {
                quotient.push('0');
            }
        }
        
        i = i + 1;
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
    /* code modified by LLM (iteration 8): fix nat type comparisons and operations */
    if sy.len() == 0 || (sy.len() == 1 && sy[0] == '0') {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut base = Vec::new();
    for i in 0..sx.len() {
        base.push(sx[i]);
    }
    
    let mut exp = Vec::new();
    for i in 0..sy.len() {
        exp.push(sy[i]);
    }
    
    let mut result = Vec::new();
    result.push('1');
    
    while exp.len() > 0 && !(exp.len() == 1 && exp[0] == '0')
        invariant
            ValidBitString(base@),
            ValidBitString(exp@),
            ValidBitString(result@),
            Str2Int(result@) * Exp_int(Str2Int(base@), Str2Int(exp@)) % Str2Int(sz@) ==
                Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
        decreases exp.len()
    {
        if exp[exp.len() - 1] == '1' {
            let mult_result = Vec::new();
            let mut temp: nat = Str2Int(result@) * Str2Int(base@);
            let mut mult_vec = Vec::new();
            
            while temp > 0nat
                invariant
                    ValidBitString(mult_vec@),
                    Str2Int(mult_vec@) + temp * Exp_int(2, mult_vec.len() as nat) ==
                        Str2Int(result@) * Str2Int(base@)
            {
                mult_vec.push(if temp % 2nat == 1nat { '1' } else { '0' });
                temp = temp / 2nat;
            }
            
            let (_, rem) = DivMod(&mult_vec, sz);
            result = rem;
        }
        
        let square_result = Vec::new();
        let mut temp2: nat = Str2Int(base@) * Str2Int(base@);
        let mut square_vec = Vec::new();
        
        while temp2 > 0nat
            invariant
                ValidBitString(square_vec@),
                Str2Int(square_vec@) + temp2 * Exp_int(2, square_vec.len() as nat) ==
                    Str2Int(base@) * Str2Int(base@)
        {
            square_vec.push(if temp2 % 2nat == 1nat { '1' } else { '0' });
            temp2 = temp2 / 2nat;
        }
        
        let (_, rem2) = DivMod(&square_vec, sz);
        base = rem2;
        
        exp.pop();
        let mut i = exp.len();
        while i > 0 && exp[i - 1] == '0'
            invariant
                0 <= i <= exp.len(),
                ValidBitString(exp@)
        {
            i = i - 1;
        }
        exp.truncate(i);
    }
    
    result
}
// </vc-code>

fn main() {}
}


