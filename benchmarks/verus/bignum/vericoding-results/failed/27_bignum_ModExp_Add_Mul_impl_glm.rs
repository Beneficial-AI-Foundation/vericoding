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
/* helper modified by LLM (iteration 3): Add char_to_int helper for converting char to int */
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
/* code modified by LLM (iteration 3): Implement proper binary addition algorithm */
{
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let max_len = s1.len().max(s2.len());
    let mut i = 0;
    
    while i < max_len
        invariant
            i <= max_len,
            result.len() == i,
            ValidBitString(result@),
            Str2Int(result@) * Exp_int(2, (max_len - i) as nat) + carry == 
                Str2Int(s1@.subrange(0, max_len as int - i as int)) + Str2Int(s2@.subrange(0, max_len as int - i as int)),
        decreases max_len - i
    {
        let digit1 = if i < s1.len() { if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let digit2 = if i < s2.len() { if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        
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
    if result.len() == 0 {
        result.push('0');
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
/* code modified by LLM (iteration 3): Simplify ModExp with proper modular reduction */
{
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let base_full = sx;
    let mut result: Vec<char> = vec!['1'];
    let mut base: Vec<char> = sx.to_vec();
    let n = sy.len();
    
    for i in 0..n
        invariant
            i <= n,
            ValidBitString(result@),
            ValidBitString(base@),
            Str2Int(result@) == Exp_int(Str2Int(sx@), Str2Int(sy@.subrange(0, i as int))) % Str2Int(sz@),
            Str2Int(base@) == Exp_int(Str2Int(sx@), Exp_int(2, i as nat)) % Str2Int(sz@),
        decreases n - i
    {
        if sy[sy.len() - 1 - i] == '1' {
            result = Mul(&result, &base);
            
            // Modular reduction
            if Str2Int(result@) >= Str2Int(sz@) {
                let mut borrow = 0;
                let mut temp_result = Vec::new();
                let max_len = result.len().max(sz.len());
                
                for j in 0..max_len {
                    let d1 = if j < result.len() && result[result.len() - 1 - j] == '1' { 1 } else { 0 };
                    let d2 = if j < sz.len() && sz[sz.len() - 1 - j] == '1' { 1 } else { 0 };
                    
                    let diff = d1 - d2 - borrow;
                    borrow = if diff < 0 { 1 } else { 0 };
                    let digit = if diff < 0 { diff + 2 } else { diff };
                    
                    temp_result.push(if digit == 1 { '1' } else { '0' });
                }
                
                // Remove leading zeros
                let mut non_zero_found = false;
                let mut final_result = Vec::new();
                temp_result.reverse();
                for k in 0..temp_result.len() {
                    if temp_result[k] == '1' || non_zero_found {
                        non_zero_found = true;
                        final_result.push(temp_result[k]);
                    }
                }
                
                if final_result.len() == 0 {
                    final_result.push('0');
                }
                
                result = final_result;
            }
        }
        
        if i < n - 1 {
            base = Mul(&base, &base);
            
            // Modular reduction
            if Str2Int(base@) >= Str2Int(sz@) {
                let mut borrow = 0;
                let mut temp_base = Vec::new();
                let max_len = base.len().max(sz.len());
                
                for j in 0..max_len {
                    let d1 = if j < base.len() && base[base.len() - 1 - j] == '1' { 1 } else { 0 };
                    let d2 = if j < sz.len() && sz[sz.len() - 1 - j] == '1' { 1 } else { 0 };
                    
                    let diff = d1 - d2 - borrow;
                    borrow = if diff < 0 { 1 } else { 0 };
                    let digit = if diff < 0 { diff + 2 } else { diff };
                    
                    temp_base.push(if digit == 1 { '1' } else { '0' });
                }
                
                // Remove leading zeros
                let mut non_zero_found = false;
                let mut final_base = Vec::new();
                temp_base.reverse();
                for k in 0..temp_base.len() {
                    if temp_base[k] == '1' || non_zero_found {
                        non_zero_found = true;
                        final_base.push(temp_base[k]);
                    }
                }
                
                if final_base.len() == 0 {
                    final_base.push('0');
                }
                
                base = final_base;
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


