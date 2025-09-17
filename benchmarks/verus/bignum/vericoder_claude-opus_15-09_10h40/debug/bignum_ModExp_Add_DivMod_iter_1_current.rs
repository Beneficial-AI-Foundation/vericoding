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
{{
    let mut carry = 0u8;
    let mut result = Vec::new();
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            0 <= i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            i <= max_len || carry == 0,
    {
        let mut sum = carry;
        
        if i < s1.len() {
            sum += if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 };
        }
        
        if i < s2.len() {
            sum += if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 };
        }
        
        result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i += 1;
    }
    
    while result.len() > 1 && result[0] == '0'
        invariant
            ValidBitString(result@),
            result.len() >= 1,
    {
        result.remove(0);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
        
        while remainder.len() > 1 && remainder[0] == '0'
            invariant
                ValidBitString(remainder@),
                remainder.len() >= 1,
        {
            remainder.remove(0);
        }
        
        let mut cmp_result = 0i32;
        if remainder.len() < divisor.len() {
            cmp_result = -1;
        } else if remainder.len() > divisor.len() {
            cmp_result = 1;
        } else {
            let mut j = 0;
            while j < remainder.len()
                invariant
                    0 <= j <= remainder.len(),
            {
                if remainder[j] < divisor[j] {
                    cmp_result = -1;
                    break;
                } else if remainder[j] > divisor[j] {
                    cmp_result = 1;
                    break;
                }
                j += 1;
            }
        }
        
        if cmp_result >= 0 {
            quotient.push('1');
            let mut borrow = 0u8;
            let mut new_remainder = Vec::new();
            let mut k = remainder.len();
            while k > 0
                invariant
                    0 <= k <= remainder.len(),
                    borrow <= 1,
            {
                k -= 1;
                let mut diff = if remainder[k] == '1' { 1i32 } else { 0i32 };
                diff -= borrow as i32;
                
                if k >= remainder.len() - divisor.len() {
                    let divisor_idx = k - (remainder.len() - divisor.len());
                    diff -= if divisor[divisor_idx] == '1' { 1 } else { 0 };
                }
                
                if diff >= 0 {
                    new_remainder.insert(0, if diff == 1 { '1' } else { '0' });
                    borrow = 0;
                } else {
                    new_remainder.insert(0, '1');
                    borrow = 1;
                }
            }
            remainder = new_remainder;
        } else {
            quotient.push('0');
        }
    }
    
    while quotient.len() > 1 && quotient[0] == '0'
        invariant
            ValidBitString(quotient@),
            quotient.len() >= 1,
    {
        quotient.remove(0);
    }
    
    while remainder.len() > 1 && remainder[0] == '0'
        invariant
            ValidBitString(remainder@),
            remainder.len() >= 1,
    {
        remainder.remove(0);
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    if remainder.len() == 0 {
        remainder.push('0');
    }
    
    (quotient, remainder)
}}
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
{{
    if sy.len() == 0 || (sy.len() == 1 && sy[0] == '0') {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    
    let mut result = Vec::new();
    result.push('1');
    
    let mut base = Vec::new();
    for i in 0..sx.len() {
        base.push(sx[i]);
    }
    
    let mut exp_bits = Vec::new();
    for i in 0..sy.len() {
        exp_bits.push(sy[i]);
    }
    
    let mut i = exp_bits.len();
    while i > 0
        invariant
            0 <= i <= exp_bits.len(),
            ValidBitString(result@),
            ValidBitString(base@),
    {
        i -= 1;
        
        let mut squared = Vec::new();
        squared.push('0');
        let mut j = 0;
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                ValidBitString(squared@),
        {
            let mut k = 0;
            while k < result.len()
                invariant
                    0 <= k <= result.len(),
            {
                if result[j] == '1' && result[k] == '1' {
                    let mut prod_term = Vec::new();
                    prod_term.push('1');
                    let shift_amount = (result.len() - 1 - j) + (result.len() - 1 - k);
                    let mut s = 0;
                    while s < shift_amount
                        invariant
                            0 <= s <= shift_amount,
                    {
                        prod_term.push('0');
                        s += 1;
                    }
                    squared = Add(&squared, &prod_term);
                }
                k += 1;
            }
            j += 1;
        }
        
        let div_result = DivMod(&squared, sz);
        result = div_result.1;
        
        if exp_bits[i] == '1' {
            let mut multiplied = Vec::new();
            multiplied.push('0');
            let mut j = 0;
            while j < result.len()
                invariant
                    0 <= j <= result.len(),
                    ValidBitString(multiplied@),
            {
                let mut k = 0;
                while k < base.len()
                    invariant
                        0 <= k <= base.len(),
                {
                    if result[j] == '1' && base[k] == '1' {
                        let mut prod_term = Vec::new();
                        prod_term.push('1');
                        let shift_amount = (result.len() - 1 - j) + (base.len() - 1 - k);
                        let mut s = 0;
                        while s < shift_amount
                            invariant
                                0 <= s <= shift_amount,
                        {
                            prod_term.push('0');
                            s += 1;
                        }
                        multiplied = Add(&multiplied, &prod_term);
                    }
                    k += 1;
                }
                j += 1;
            }
            let div_result = DivMod(&multiplied, sz);
            result = div_result.1;
        }
    }
    
    result
}}
// </vc-code>

fn main() {}
}


