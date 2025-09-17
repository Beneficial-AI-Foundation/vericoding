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
/* helper modified by LLM (iteration 2): Added decreases clauses to loops */
exec fn subtract_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
        Str2Int(a@) >= Str2Int(b@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) - Str2Int(b@)
{
    let mut result = Vec::<char>::new();
    let mut borrow = 0u8;
    let mut i = 0;
    
    while i < a.len() || i < b.len() || borrow > 0
        invariant
            0 <= i <= a.len(),
            borrow == 0 || borrow == 1,
            ValidBitString(result@)
        decreases (if i < a.len() { a.len() - i } else { 0 }) + (if i < b.len() { b.len() - i } else { 0 }) + borrow
    {
        let a_bit = if i < a.len() { if a[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let b_bit = if i < b.len() { if b[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        
        let diff = if a_bit >= b_bit + borrow {
            borrow = 0;
            a_bit - b_bit - borrow
        } else {
            let new_val = a_bit + 2 - b_bit - borrow;
            borrow = 1;
            new_val
        };
        
        result.push(if diff == 1 { '1' } else { '0' });
        i = i + 1;
    }
    
    // Remove leading zeros
    while result.len() > 1 && result[result.len() - 1] == '0'
        invariant
            result.len() >= 1,
            ValidBitString(result@)
        decreases result.len()
    {
        result.pop();
    }
    
    result
}

exec fn compare_binary(a: &[char], b: &[char]) -> (res: bool)
    requires
        ValidBitString(a@),
        ValidBitString(b@)
    ensures
        res == (Str2Int(a@) >= Str2Int(b@))
{
    if a.len() != b.len() {
        return a.len() > b.len();
    }
    
    let mut i = a.len();
    while i > 0
        invariant
            0 <= i <= a.len()
        decreases i
    {
        i = i - 1;
        if a[i] != b[i] {
            return a[i] == '1';
        }
    }
    
    true
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
{
    /* code modified by LLM (iteration 2): Added decreases clauses to all loops */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    // Initialize remainder with dividend
    let mut i = 0;
    while i < dividend.len()
        invariant
            0 <= i <= dividend.len(),
            remainder@.len() == i,
            ValidBitString(remainder@)
        decreases dividend.len() - i
    {
        remainder.push(dividend[i]);
        i = i + 1;
    }
    
    // Perform division by repeated subtraction
    while compare_binary(&remainder, divisor)
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@)
        decreases Str2Int(remainder@)
    {
        remainder = subtract_binary(&remainder, divisor);
        
        // Increment quotient
        let mut carry = 1u8;
        let mut j = 0;
        let mut new_quotient = Vec::<char>::new();
        
        while j < quotient.len() || carry > 0
            invariant
                0 <= j,
                carry == 0 || carry == 1,
                ValidBitString(new_quotient@)
            decreases (if j < quotient.len() { quotient.len() - j } else { 0 }) + carry
        {
            let q_bit = if j < quotient.len() { if quotient[j] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
            let sum = q_bit + carry;
            
            new_quotient.push(if sum % 2 == 1 { '1' } else { '0' });
            carry = sum / 2;
            j = j + 1;
        }
        
        quotient = new_quotient;
    }
    
    // Handle empty quotient case
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

