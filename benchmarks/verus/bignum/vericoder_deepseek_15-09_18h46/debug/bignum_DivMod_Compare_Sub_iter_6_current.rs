use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added missing compare_strings and subtract_strings functions */
fn compare_strings(a: &[char], b: &[char]) -> bool
    requires ValidBitString(a@), ValidBitString(b@)
    ensures result == (Str2Int(a@) >= Str2Int(b@))
{
    if a.len() > b.len() {
        true
    } else if a.len() < b.len() {
        false
    } else {
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                forall |j: int| 0 <= j < i ==> a[j] == b[j]
            decreases a.len() - i
        {
            if a[i] != b[i] {
                return a[i] > b[i];
            }
            i += 1;
        }
        true
    }
}

fn subtract_strings(a: &[char], b: &[char]) -> Vec<char>
    requires ValidBitString(a@), ValidBitString(b@), Str2Int(a@) >= Str2Int(b@)
    ensures ValidBitString(result@), Str2Int(result@) == Str2Int(a@) - Str2Int(b@)
{
    let mut result = Vec::new();
    let mut borrow = 0;
    let mut i = a.len() as int - 1;
    let mut j = b.len() as int - 1;
    
    while i >= 0
        invariant
            i >= -1,
            ValidBitString(result@),
            borrow == 0 || borrow == 1,
            Str2Int(a.subrange(0, i + 1)) + borrow * (pow2(i + 1)) == 
                Str2Int(b.subrange(0, j + 1)) + Str2Int(result@)
        decreases i + 1
    {
        let a_digit = if i >= 0 { if a[i as usize] == '1' { 1 } else { 0 } } else { 0 };
        let b_digit = if j >= 0 { if b[j as usize] == '1' { 1 } else { 0 } } else { 0 };
        
        let mut diff = a_digit - b_digit - borrow;
        if diff < 0 {
            diff += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        
        result.push(if diff == 1 { '1' } else { '0' });
        
        i -= 1;
        j -= 1;
    }
    
    result.reverse();
    
    // Remove leading zeros
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    
    result
}

spec fn pow2(n: int) -> nat
    decreases n
{
    if n <= 0 {
        1nat
    } else {
        2 * pow2(n - 1)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors by using new helper functions */
{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    if !compare_strings(dividend, divisor) {
        quotient.push('0');
        remainder.extend_from_slice(dividend);
        return (quotient, remainder);
    }
    
    let mut current = Vec::new();
    let mut i = 0;
    
    while i < dividend.len()
        invariant
            0 <= i <= dividend.len(),
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            ValidBitString(current@),
            Str2Int(dividend@) == Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(remainder@),
            Str2Int(remainder@) < Str2Int(divisor@),
            Str2Int(current@) == Str2Int(dividend.subrange(0, i as int))
        decreases dividend.len() - i
    {
        current.push(dividend[i]);
        
        if compare_strings(&current, divisor) {
            quotient.push('1');
            let subtracted = subtract_strings(&current, divisor);
            current = subtracted;
        } else {
            quotient.push('0');
        }
        
        i += 1;
    }
    
    remainder = current;
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

