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
    /* code modified by LLM (iteration 2): Fixed type mismatches by using nat types and explicit casts */
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i = 0nat;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len,
            carry <= 1,
            ValidBitString(result@)
    {
        let bit1 = if i < s1.len() { if s1[(s1.len() - 1 - i) as usize] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let bit2 = if i < s2.len() { if s2[(s2.len() - 1 - i) as usize] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let sum = bit1 + bit2 + carry;
        let result_bit = sum % 2;
        carry = sum / 2;
        
        if result_bit == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
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
    /* code modified by LLM (iteration 2): Fixed type mismatches by using nat literals */
    if Str2Int(s1@) == 0nat || Str2Int(s2@) == 0nat {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i = 0nat;
    while i < s2.len()
        invariant
            i <= s2.len(),
            ValidBitString(result@)
    {
        if s2[(s2.len() - 1 - i) as usize] == '1' {
            let mut shifted_s1 = Vec::<char>::new();
            let mut j = 0nat;
            while j < s1.len()
                invariant
                    j <= s1.len(),
                    ValidBitString(shifted_s1@)
            {
                shifted_s1.push(s1[j as usize]);
                j += 1;
            }
            
            let mut k = 0nat;
            while k < i
                invariant
                    k <= i,
                    ValidBitString(shifted_s1@)
            {
                shifted_s1.push('0');
                k += 1;
            }
            
            result = Add(&result, &shifted_s1);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatches by using nat types and proper sequence indexing */
    if n == 0int {
        if sy@.len() > 0nat && sy@.index(0) == '1' && (sy@.len() == 1nat || (sy@.len() > 1nat && forall |k: int| 1 <= k < sy@.len() as int ==> sy@.index(k) == '0')) {
            let mut result = Vec::<char>::new();
            result.push('1');
            return result;
        } else {
            let mut result = Vec::<char>::new();
            result.push('1');
            return result;
        }
    }
    
    if Str2Int(sy@) == 0nat {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    if sy@.index((sy@.len() - 1nat) as int) == '0' {
        let mut sy_half = Vec::<char>::new();
        let mut i = 0nat;
        while i < sy@.len() - 1nat
            invariant
                i <= sy@.len() - 1nat,
                ValidBitString(sy_half@)
        {
            sy_half.push(sy@.index(i as int));
            i += 1;
        }
        
        if sy_half.len() == 0 {
            sy_half.push('0');
        }
        
        let temp_result = ModExpPow2(sx, &sy_half, n - 1int, sz);
        return Mul(&temp_result, &temp_result);
    } else {
        let mut sy_minus_one = Vec::<char>::new();
        let mut found_one = false;
        let mut i = 0nat;
        
        while i < sy@.len()
            invariant
                i <= sy@.len(),
                ValidBitString(sy_minus_one@)
        {
            if !found_one {
                if sy@.index((sy@.len() - 1nat - i) as int) == '1' {
                    sy_minus_one.insert(0, '0');
                    found_one = true;
                } else {
                    sy_minus_one.insert(0, '1');
                }
            } else {
                sy_minus_one.insert(0, sy@.index((sy@.len() - 1nat - i) as int));
            }
            i += 1;
        }
        
        let temp_result = ModExpPow2(sx, &sy_minus_one, n, sz);
        let mul_result = Mul(&temp_result, sx);
        return mul_result;
    }
}
// </vc-code>

fn main() {}
}
