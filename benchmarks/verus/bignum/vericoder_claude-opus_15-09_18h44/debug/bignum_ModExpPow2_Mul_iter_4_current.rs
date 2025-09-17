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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut carry = 0u32;
    
    for i in 0..s1.len() {
        let mut partial = Vec::<char>::new();
        carry = 0;
        
        // Add zeros for position
        for _ in 0..i {
            partial.push('0');
        }
        
        // Multiply s1[i] by each digit of s2
        for j in 0..s2.len() {
            let d1 = if s1[s1.len() - 1 - i] == '1' { 1u32 } else { 0u32 };
            let d2 = if s2[s2.len() - 1 - j] == '1' { 1u32 } else { 0u32 };
            let prod = d1 * d2 + carry;
            partial.push(if prod % 2 == 1 { '1' } else { '0' });
            carry = prod / 2;
        }
        
        if carry > 0 {
            partial.push('1');
        }
        
        // Add partial to result
        if i == 0 {
            result = partial;
        } else {
            let mut sum = Vec::<char>::new();
            carry = 0;
            let max_len = if result.len() > partial.len() { result.len() } else { partial.len() };
            
            for k in 0..max_len {
                let r = if k < result.len() { if result[k] == '1' { 1u32 } else { 0u32 } } else { 0u32 };
                let p = if k < partial.len() { if partial[k] == '1' { 1u32 } else { 0u32 } } else { 0u32 };
                let s = r + p + carry;
                sum.push(if s % 2 == 1 { '1' } else { '0' });
                carry = s / 2;
            }
            
            if carry > 0 {
                sum.push('1');
            }
            result = sum;
        }
    }
    
    // Reverse to get proper bit order
    let mut final_result = Vec::<char>::new();
    for i in 0..result.len() {
        final_result.push(result[result.len() - 1 - i]);
    }
    
    // Remove leading zeros
    while final_result.len() > 1 && final_result[0] == '0' {
        final_result.remove(0);
    }
    
    if final_result.len() == 0 {
        final_result.push('0');
    }
    
    final_result
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
    if n == 0 {
        // y = 1, so x^1 mod z
        let mut x_val = Vec::<char>::new();
        for i in 0..sx.len() {
            x_val.push(sx[i]);
        }
        
        // Compute modulo
        let mut dividend = x_val;
        let mut remainder = Vec::<char>::new();
        
        // Simple modulo implementation
        let mut temp = 0u64;
        for i in 0..dividend.len() {
            temp = temp * 2 + if dividend[i] == '1' { 1 } else { 0 };
        }
        
        let mut divisor = 0u64;
        for i in 0..sz.len() {
            divisor = divisor * 2 + if sz[i] == '1' { 1 } else { 0 };
        }
        
        let rem = temp % divisor;
        
        if rem == 0 {
            remainder.push('0');
        } else {
            let mut r = rem;
            let mut bits = Vec::<char>::new();
            while r > 0 {
                bits.push(if r % 2 == 1 { '1' } else { '0' });
                r = r / 2;
            }
            for i in 0..bits.len() {
                remainder.push(bits[bits.len() - 1 - i]);
            }
        }
        
        return remainder;
    } else {
        // y = 2^n, so compute x^(2^(n-1)) first
        let mut y_half = Vec::<char>::new();
        y_half.push('1');
        for _ in 0..n-1 {
            y_half.push('0');
        }
        
        let half_result = ModExpPow2(sx, &y_half, n - 1, sz);
        
        // Square the result and take mod
        let squared = Mul(&half_result, &half_result);
        
        // Compute modulo
        let mut temp = 0u64;
        for i in 0..squared.len() {
            temp = temp * 2 + if squared[i] == '1' { 1 } else { 0 };
        }
        
        let mut divisor = 0u64;
        for i in 0..sz.len() {
            divisor = divisor * 2 + if sz[i] == '1' { 1 } else { 0 };
        }
        
        let rem = temp % divisor;
        let mut result = Vec::<char>::new();
        
        if rem == 0 {
            result.push('0');
        } else {
            let mut r = rem;
            let mut bits = Vec::<char>::new();
            while r > 0 {
                bits.push(if r % 2 == 1 { '1' } else { '0' });
                r = r / 2;
            }
            for i in 0..bits.len() {
                result.push(bits[bits.len() - 1 - i]);
            }
        }
        
        return result;
    }
}
// </vc-code>

fn main() {}
}


