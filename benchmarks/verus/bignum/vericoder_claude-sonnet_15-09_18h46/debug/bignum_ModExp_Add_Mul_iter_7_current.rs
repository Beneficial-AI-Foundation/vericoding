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
    /* code modified by LLM (iteration 7): fixed nat literals to use nat suffix */
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i = s1.len();
    let mut j = s2.len();
    
    while i > 0 || j > 0 || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 2,
            i <= s1.len(),
            j <= s2.len()
    {
        let bit1 = if i > 0 { 
            i = i - 1;
            if s1[i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let bit2 = if j > 0 {
            j = j - 1;
            if s2[j] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(result_bit);
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
    /* code modified by LLM (iteration 7): fixed nat literals and int literals for proper type compatibility */
    if s1@.len() == 0nat || s2@.len() == 0nat || (s1@.len() == 1nat && s1@.index(0int) == '0') || (s2@.len() == 1nat && s2@.index(0int) == '0') {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i = 0;
    while i < s2.len()
        invariant
            ValidBitString(result@),
            i <= s2.len()
    {
        if s2[s2.len() - 1 - i] == '1' {
            let shifted_s1 = {
                let mut temp = Vec::<char>::new();
                for bit in s1.iter() {
                    temp.push(*bit);
                }
                for _ in 0..i {
                    temp.push('0');
                }
                temp
            };
            result = Add(&result, &shifted_s1);
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
    /* code modified by LLM (iteration 7): fixed nat literals and int literals for proper type compatibility */
    if sy@.len() == 1nat && sy@.index(0int) == '0' {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('1');
    
    let mut base = Vec::<char>::new();
    for bit in sx.iter() {
        base.push(*bit);
    }
    
    let mut exp = Vec::<char>::new();
    for bit in sy.iter() {
        exp.push(*bit);
    }
    
    while exp@.len() > 1nat || (exp@.len() == 1nat && exp@.index(0int) == '1')
        invariant
            ValidBitString(result@),
            ValidBitString(base@),
            ValidBitString(exp@)
        decreases exp@.len()
    {
        proof {
            let ghost last_idx: int = exp@.len() - 1;
            assert(last_idx >= 0);
        }
        if exp@.len() > 0nat && exp[exp.len() - 1] == '1' {
            result = Mul(&result, &base);
            let mut temp_result = Vec::<char>::new();
            let mut carry = 0;
            for i in 0..result.len() {
                let digit = if result[i] == '1' { 1 } else { 0 };
                temp_result.push(if digit == 1 { '1' } else { '0' });
            }
            result = temp_result;
        }
        
        base = Mul(&base, &base);
        
        let mut new_exp = Vec::<char>::new();
        let mut carry = 0;
        let mut k = exp.len();
        while k > 0 {
            k = k - 1;
            let val = if exp[k] == '1' { 1 } else { 0 };
            let new_val = (val + carry) / 2;
            carry = (val + carry) % 2 * 10;
            if k > 0 || new_val > 0 {
                new_exp.insert(0, if new_val == 1 { '1' } else { '0' });
            }
        }
        if new_exp.len() == 0 {
            new_exp.push('0');
        }
        exp = new_exp;
    }
    
    result
}
// </vc-code>

fn main() {}
}


