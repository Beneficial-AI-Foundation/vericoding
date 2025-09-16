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
/* helper modified by LLM (iteration 5): Remove assume statements and fix subtraction logic */
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
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            borrow == 0 || borrow == 1,
            ValidBitString(result@),
            result@.len() == i
        decreases a.len() - i
    {
        let a_bit = if a[i] == '1' { 1u8 } else { 0u8 };
        let b_bit = if i < b.len() { if b[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        
        let mut diff: u8;
        if a_bit >= b_bit + borrow {
            diff = a_bit - b_bit - borrow;
            borrow = 0;
        } else {
            diff = 2 + a_bit - b_bit - borrow;
            borrow = 1;
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
    
    if result.len() == 0 {
        result.push('0');
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
    if a.len() > b.len() {
        return true;
    }
    if a.len() < b.len() {
        return false;
    }
    
    // Same length, compare from MSB
    let mut i = a.len();
    while i > 0
        invariant
            0 <= i <= a.len(),
            a.len() == b.len()
        decreases i
    {
        i = i - 1;
        if a[i] == '1' && b[i] == '0' {
            return true;
        }
        if a[i] == '0' && b[i] == '1' {
            return false;
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
    /* code modified by LLM (iteration 5): Simplify implementation and fix invariants */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    // Initialize remainder with dividend
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            0 <= i <= dividend.len(),
            remainder@.len() == i,
            ValidBitString(remainder@),
            forall |j: int| 0 <= j && j < i ==> remainder@[j] == dividend@[j]
        decreases dividend.len() - i
    {
        remainder.push(dividend[i]);
        i = i + 1;
    }
    
    // Initialize quotient with zero
    quotient.push('0');
    
    // Perform division by repeated subtraction
    while compare_binary(&remainder, divisor)
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            quotient@.len() >= 1
        decreases remainder.len()
    {
        remainder = subtract_binary(&remainder, divisor);
        
        // Increment quotient by 1
        let mut carry = 1u8;
        let mut j: usize = 0;
        let mut new_quotient = Vec::<char>::new();
        
        while j < quotient.len()
            invariant
                0 <= j <= quotient.len(),
                carry == 0 || carry == 1,
                ValidBitString(new_quotient@),
                new_quotient@.len() == j
            decreases quotient.len() - j
        {
            let q_bit = if quotient[j] == '1' { 1u8 } else { 0u8 };
            let sum = q_bit + carry;
            
            new_quotient.push(if sum % 2 == 1 { '1' } else { '0' });
            carry = sum / 2;
            j = j + 1;
        }
        
        if carry > 0 {
            new_quotient.push('1');
        }
        
        quotient = new_quotient;
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

