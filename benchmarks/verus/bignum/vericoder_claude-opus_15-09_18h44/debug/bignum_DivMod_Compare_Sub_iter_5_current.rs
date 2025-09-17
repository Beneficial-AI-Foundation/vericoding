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
/* helper modified by LLM (iteration 5): Fixed index bounds in compare_binary and subtract_binary */
exec fn compare_binary(a: &[char], b: &[char]) -> (res: bool)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
    ensures
        res == (Str2Int(a@) >= Str2Int(b@)),
{
    let len_a = a.len();
    let len_b = b.len();
    
    // First compare lengths
    if len_a > len_b {
        return true;
    } else if len_a < len_b {
        return false;
    }
    
    // Same length, compare digit by digit from MSB (end) to LSB (start)
    let mut i = len_a;
    while i > 0
        invariant
            0 <= i <= len_a,
            len_a == len_b,
            ValidBitString(a@),
            ValidBitString(b@),
            forall |j: int| i <= j && j < len_a ==> 0 <= j < a@.len() && 0 <= j < b@.len() && a@[j] == b@[j],
        decreases i
    {
        let idx = (i - 1) as usize;
        if idx < a.len() && idx < b.len() {
            if a[idx] == '1' && b[idx] == '0' {
                return true;
            } else if a[idx] == '0' && b[idx] == '1' {
                return false;
            }
        }
        i = i - 1;
    }
    true
}

exec fn subtract_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
        Str2Int(a@) >= Str2Int(b@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) - Str2Int(b@),
{
    let len_a = a.len();
    let len_b = b.len();
    let mut result = Vec::new();
    let mut borrow = 0u8;
    let mut i = 0usize;
    
    // Process from LSB to MSB
    while i < len_a
        invariant
            0 <= i <= len_a,
            ValidBitString(a@),
            ValidBitString(b@),
            ValidBitString(result@),
            borrow == 0 || borrow == 1,
        decreases len_a - i
    {
        let digit_a = if i < a.len() && a[i] == '1' { 1u8 } else { 0u8 };
        let digit_b = if i < b.len() && b[i] == '1' { 1u8 } else { 0u8 };
        
        let sum = digit_a + 2 * borrow;
        if sum >= digit_b {
            let diff = sum - digit_b;
            result.push(if diff % 2 == 1 { '1' } else { '0' });
            borrow = 0;
        } else {
            let diff = sum + 2 - digit_b;
            result.push(if diff == 1 { '1' } else { '0' });
            borrow = 1;
        }
        i = i + 1;
    }
    
    // Ensure at least one digit
    if result.len() == 0 {
        result.push('0');
    }
    
    // Remove leading zeros from MSB end
    while result.len() > 1 && result[result.len() - 1] == '0'
        invariant
            result.len() >= 1,
            ValidBitString(result@),
        decreases result.len()
    {
        result.pop();
    }
    
    result
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
/* code modified by LLM (iteration 5): Simplified DivMod implementation with proper initialization and bounds checking */
{
    let mut quotient = Vec::new();
    quotient.push('0');
    let mut remainder = Vec::new();
    
    // Initialize remainder with dividend
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
    }
    
    // Handle zero dividend
    if dividend.len() == 0 || (dividend.len() == 1 && dividend[0] == '0') {
        return (quotient, remainder);
    }
    
    // Check if dividend < divisor
    if !compare_binary(&remainder, divisor) {
        return (quotient, remainder);
    }
    
    // Perform long division using repeated subtraction
    let mut count = 0u64;
    while compare_binary(&remainder, divisor)
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            ValidBitString(divisor@),
            Str2Int(divisor@) > 0,
            quotient.len() >= 1,
        decreases Str2Int(remainder@)
    {
        remainder = subtract_binary(&remainder, divisor);
        count = count + 1;
        
        // Convert count to binary and store in quotient
        quotient = Vec::new();
        let mut temp_count = count;
        if temp_count == 0 {
            quotient.push('0');
        } else {
            let mut binary_digits = Vec::new();
            while temp_count > 0
                invariant
                    ValidBitString(binary_digits@),
                decreases temp_count
            {
                if temp_count % 2 == 1 {
                    binary_digits.push('1');
                } else {
                    binary_digits.push('0');
                }
                temp_count = temp_count / 2;
            }
            // Binary digits are in reverse order (LSB first), copy them to quotient
            for j in 0..binary_digits.len() {
                quotient.push(binary_digits[j]);
            }
        }
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

