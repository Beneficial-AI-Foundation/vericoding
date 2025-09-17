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
/* helper modified by LLM (iteration 2): Add char_to_int helper for converting char to int */
spec fn char_to_int(c: char) -> int
{
    if c == '1' { 1 } else { 0 }
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix int type usage by using usize instead for exec code */
{
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let max_len = s1.len().max(s2.len());
    let mut i: usize = if max_len > 0 { max_len - 1 } else { 0 };
    
    while i < max_len
        invariant
            i <= max_len,
            result.len() == max_len - i,
            ValidBitString(result@),
            Str2Int(result@) + carry * Exp_int(2, (result.len() as nat)) == 
                Str2Int(s1@.subrange(0, i + 1)) + Str2Int(s2@.subrange(0, i + 1)),
        decreases max_len - i
    {
        let digit1 = if i < s1.len() && s1[s1.len() - 1 - i] == '1' { 1 } else { 0 };
        let digit2 = if i < s2.len() && s2[s2.len() - 1 - i] == '1' { 1 } else { 0 };
        
        let sum = digit1 + digit2 + carry;
        let new_digit = sum % 2;
        carry = sum / 2;
        
        result.push(if new_digit == 1 { '1' } else { '0' });
        i += 1;
    }
    
    if carry > 0 {
        result.push('1');
    }
    
    result.reverse();
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
/* code modified by LLM (iteration 2): Fix sequence subrange indexing and helper calls */
{
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let mut half_y = Vec::<char>::new();
    for i in 0..sy.len() - 1 {
        half_y.push(sy[i]);
    }
    
    let half_exp = ModExp(sx, &half_y, sz);
    
    let mut temp = Mul(&half_exp, &half_exp);
    let temp_mod = {
        let mut result = Vec::<char>::new();
        
        // Modular reduction
        let mut done = false;
        let mut comparison = 0;
        
        // Compare temp with sz
        let mut i = 0;
        while i < temp.len() && i < sz.len()
            invariant
                i <= temp.len() && i <= sz.len(),
            decreases temp.len() - i
        {
            if temp[i] != sz[i] {
                comparison = if temp[i] == '1' { 1 } else { -1 };
                done = true;
                break;
            }
            i += 1;
        }
        
        if !done {
            if temp.len() > sz.len() {
                comparison = 1;
            } else if temp.len() < sz.len() {
                comparison = -1;
            } else {
                comparison = 0;
            }
        }
        
        if comparison >= 0 {
            // Perform subtraction
            let mut borrow = 0;
            let mut subtract_result = Vec::<char>::new();
            let max_len = temp.len().max(sz.len());
            
            for j in 0..max_len {
                let d1 = if j < temp.len() && temp[temp.len() - 1 - j] == '1' { 1 } else { 0 };
                let d2 = if j < sz.len() && sz[sz.len() - 1 - j] == '1' { 1 } else { 0 };
                
                let diff = d1 - d2 - borrow;
                borrow = if diff < 0 { 1 } else { 0 };
                let digit = if diff < 0 { diff + 2 } else { diff };
                
                subtract_result.push(if digit == 1 { '1' } else { '0' });
            }
            
            // Remove leading zeros
            let mut non_zero_found = false;
            let mut final_result = Vec::<char>::new();
            subtract_result.reverse();
            for k in 0..subtract_result.len() {
                if subtract_result[k] == '1' || non_zero_found {
                    non_zero_found = true;
                    final_result.push(subtract_result[k]);
                }
            }
            
            if final_result.len() == 0 {
                final_result.push('0');
            }
            
            result = final_result;
        } else {
            result = temp;
        }
        
        result
    };
    
    if sy[sy.len() - 1] == '1' {
        let temp2 = Mul(&temp_mod, sx);
        
        let mut result = Vec::<char>::new();
        
        // Modular reduction for temp2
        let mut done = false;
        let mut comparison = 0;
        
        // Compare temp2 with sz
        let mut i = 0;
        while i < temp2.len() && i < sz.len()
            invariant
                i <= temp2.len() && i <= sz.len(),
            decreases temp2.len() - i
        {
            if temp2[i] != sz[i] {
                comparison = if temp2[i] == '1' { 1 } else { -1 };
                done = true;
                break;
            }
            i += 1;
        }
        
        if !done {
            if temp2.len() > sz.len() {
                comparison = 1;
            } else if temp2.len() < sz.len() {
                comparison = -1;
            } else {
                comparison = 0;
            }
        }
        
        if comparison >= 0 {
            // Perform subtraction
            let mut borrow = 0;
            let mut subtract_result = Vec::<char>::new();
            let max_len = temp2.len().max(sz.len());
            
            for j in 0..max_len {
                let d1 = if j < temp2.len() && temp2[temp2.len() - 1 - j] == '1' { 1 } else { 0 };
                let d2 = if j < sz.len() && sz[sz.len() - 1 - j] == '1' { 1 } else { 0 };
                
                let diff = d1 - d2 - borrow;
                borrow = if diff < 0 { 1 } else { 0 };
                let digit = if diff < 0 { diff + 2 } else { diff };
                
                subtract_result.push(if digit == 1 { '1' } else { '0' });
            }
            
            // Remove leading zeros
            let mut non_zero_found = false;
            let mut final_result = Vec::<char>::new();
            subtract_result.reverse();
            for k in 0..subtract_result.len() {
                if subtract_result[k] == '1' || non_zero_found {
                    non_zero_found = true;
                    final_result.push(subtract_result[k]);
                }
            }
            
            if final_result.len() == 0 {
                final_result.push('0');
            }
            
            result = final_result;
        } else {
            result = temp2;
        }
        
        result
    } else {
        temp_mod
    }
}
// </vc-code>

fn main() {}
}


