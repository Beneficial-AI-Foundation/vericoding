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
    let mut i = (s1.len() as int).max(s2.len() as int) - 1;
    
    while i >= 0
        invariant
            0 <= i + 1 <= (s1.len() as int).max(s2.len() as int),
            result.len() == (s1.len() as int).max(s2.len() as int) - i - 1,
            ValidBitString(result@),
            Str2Int(result@) + carry * Exp_int(2, (result.len() as nat)) == 
                Str2Int(s1@.subrange(0, i + 1)) + Str2Int(s2@.subrange(0, i + 1)),
        decreases i
    {
        let digit1 = if i < s1.len() as int && s1[i as usize] == '1' { 1 } else { 0 };
        let digit2 = if i < s2.len() as int && s2[i as usize] == '1' { 1 } else { 0 };
        
        let sum = digit1 + digit2 + carry;
        let new_digit = sum % 2;
        carry = sum / 2;
        
        result.push(if new_digit == 1 { '1' } else { '0' });
        i -= 1;
    }
    
    if carry > 0 {
        result.push('1');
    }
    
    result.reverse();
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
    
    let mut j = 0;
    
    while j < s2.len()
        invariant
            0 <= j <= s2.len(),
            result.len() > 0,
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, j)),
        decreases s2.len() - j
    {
        if s2[s2.len() - 1 - j] == '1' {
            let mut partial_result = Vec::<char>::new();
            for _ in 0..j {
                partial_result.push('0');
            }
            for i in 0..s1.len() {
                partial_result.push(s1[s1.len() - 1 - i]);
            }
            partial_result.reverse();
            
            let temp = Add(&result, &partial_result);
            result = temp;
        }
        j += 1;
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
    
    let half_y = sy.subrange(0, sy.len() as int - 1);
    let half_exp = ModExp(sx, &half_y.as_slice(), sz);
    
    let mut temp = Mul(&half_exp, &half_exp);
    let temp_mod = {
        let s_val = Str2Int(temp@);
        let m_val = Str2Int(sz@);
        let mod_val = s_val % m_val;
        
        let mut result = Vec::<char>::new();
        if mod_val == 0 {
            result.push('0');
        } else {
            let mut bits = Vec::<char>::new();
            let mut val = mod_val;
            while val > 0
                invariant
                    val >= 0,
                    Str2Int(bits@) * Exp_int(2, bits.len() as nat) + val == mod_val,
                decreases val
            {
                bits.push(if val % 2 == 1 { '1' } else { '0' });
                val /= 2;
            }
            bits.reverse();
            result = bits;
        }
        
        result
    };
    
    if sy[sy.len() - 1] == '1' {
        let mut temp2 = Mul(&temp_mod, sx);
        let result = {
            let s_val = Str2Int(temp2@);
            let m_val = Str2Int(sz@);
            let mod_val = s_val % m_val;
            
            let mut result = Vec::<char>::new();
            if mod_val == 0 {
                result.push('0');
            } else {
                let mut bits = Vec::<char>::new();
                let mut val = mod_val;
                while val > 0
                    invariant
                        val >= 0,
                        Str2Int(bits@) * Exp_int(2, bits.len() as nat) + val == mod_val,
                    decreases val
                {
                    bits.push(if val % 2 == 1 { '1' } else { '0' });
                    val /= 2;
                }
                bits.reverse();
                result = bits;
            }
            
            result
        };
        result
    } else {
        temp_mod
    }
}
// </vc-code>

fn main() {}
}


