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
/* helper modified by LLM (iteration 9): Fixed &mut parameter issue by passing values instead of references */
fn compare_strings(a: Vec<char>, b: Vec<char>) -> (result: bool)
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

fn subtract_strings(a: Vec<char>, b: Vec<char>) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@), Str2Int(a@) >= Str2Int(b@)
    ensures ValidBitString(result@), Str2Int(result@) == Str2Int(a@) - Str2Int(b@)
{
    let mut result = Vec::new();
    let mut borrow = 0;
    let mut i: usize = a.len();
    let mut j: usize = b.len();
    
    while i > 0
        invariant
            i >= 0,
            ValidBitString(result@),
            borrow == 0 || borrow == 1
        decreases i
    {
        i -= 1;
        if j > 0 {
            j -= 1;
        }
        
        let a_digit = if a[i] == '1' { 1 } else { 0 };
        let b_digit = if j < b.len() { if b[j] == '1' { 1 } else { 0 } } else { 0 };
        
        let mut diff = a_digit - b_digit - borrow;
        if diff < 0 {
            diff += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        
        result.push(if diff == 1 { '1' } else { '0' });
    }
    
    let reversed = result.into_iter().rev().collect();
    
    let mut trimmed = reversed;
    while trimmed.len() > 1 && trimmed[0] == '0' {
        trimmed.remove(0);
    }
    
    trimmed
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
/* code modified by LLM (iteration 9): Fixed calls to helper functions with Vec instead of &[char] */
{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    let dividend_vec = dividend.to_vec();
    let divisor_vec = divisor.to_vec();
    
    let comp_result = compare_strings(dividend_vec.clone(), divisor_vec.clone());
    if !comp_result {
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
            Str2Int(dividend@) == Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(current@),
            Str2Int(current@) < Str2Int(divisor@)
        decreases dividend.len() - i
    {
        current.push(dividend[i]);
        
        let comp_current = compare_strings(current.clone(), divisor_vec.clone());
        if comp_current {
            quotient.push('1');
            let subtracted_result = subtract_strings(current, divisor_vec.clone());
            current = subtracted_result;
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

