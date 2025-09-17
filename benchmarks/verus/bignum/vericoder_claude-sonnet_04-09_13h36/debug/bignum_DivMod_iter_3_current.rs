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
spec fn is_zero(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> s[i] == '0'
}

spec fn bit_ge(a: Seq<char>, b: Seq<char>) -> bool
    recommends ValidBitString(a) && ValidBitString(b)
{
    Str2Int(a) >= Str2Int(b)
}

spec fn bit_sub_spec(a: Seq<char>, b: Seq<char>) -> Seq<char>
    recommends ValidBitString(a) && ValidBitString(b) && bit_ge(a, b)
{
    arbitrary()
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s.push('0'))
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{}

proof fn lemma_str2int_empty()
    ensures Str2Int(seq![]) == 0
{}

proof fn lemma_valid_empty()
    ensures ValidBitString(seq![])
{}

exec fn bit_compare(a: &[char], b: &[char]) -> (result: bool)
    requires ValidBitString(a@) && ValidBitString(b@)
    ensures result == bit_ge(a@, b@)
{
    if a.len() > b.len() { return true; }
    if a.len() < b.len() { return false; }
    
    let mut i = 0;
    while i < a.len()
        invariant 0 <= i <= a.len()
        invariant a.len() == b.len()
        invariant forall |j: int| 0 <= j < i ==> a@[j] == b@[j]
    {
        if a[i] > b[i] { return true; }
        if a[i] < b[i] { return false; }
        i += 1;
    }
    true
}

exec fn bit_subtract(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@) && ValidBitString(b@)
    requires bit_ge(a@, b@)
    ensures ValidBitString(result@)
    ensures Str2Int(result@) == Str2Int(a@) - Str2Int(b@)
{
    let mut result = Vec::new();
    let mut borrow = false;
    let mut i = 0;
    
    while i < a.len().max(b.len())
        invariant 0 <= i <= a.len().max(b.len())
        invariant ValidBitString(result@)
    {
        let a_bit = if i < a.len() { a[a.len() - 1 - i] == '1' } else { false };
        let b_bit = if i < b.len() { b[b.len() - 1 - i] == '1' } else { false };
        
        let diff = (a_bit as u8) - (b_bit as u8) - (borrow as u8);
        
        if diff >= 0 {
            result.push(if diff == 1 { '1' } else { '0' });
            borrow = false;
        } else {
            result.push('1');
            borrow = true;
        }
        i += 1;
    }
    
    result.reverse();
    
    // Remove leading zeros
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    if dividend.len() == 0 {
        quotient.push('0');
        remainder.push('0');
        return (quotient, remainder);
    }
    
    // Initialize remainder to empty
    remainder.push('0');
    
    let mut i = 0;
    while i < dividend.len()
        invariant 0 <= i <= dividend.len()
        invariant ValidBitString(quotient@)
        invariant ValidBitString(remainder@)
        invariant remainder.len() > 0
    {
        // Shift remainder left and add next bit
        remainder = {
            let mut temp = Vec::new();
            let mut j = 0;
            while j < remainder.len() {
                temp.push(remainder[j]);
                j += 1;
            }
            temp.push(dividend[i]);
            temp
        };
        
        // Remove leading zeros from remainder
        while remainder.len() > 1 && remainder[0] == '0' {
            remainder.remove(0);
        }
        
        // Check if remainder >= divisor
        if bit_compare(&remainder, divisor) {
            quotient.push('1');
            remainder = bit_subtract(&remainder, divisor);
        } else {
            quotient.push('0');
        }
        
        i += 1;
    }
    
    // Remove leading zeros from quotient
    while quotient.len() > 1 && quotient[0] == '0' {
        quotient.remove(0);
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

fn main() {}
}