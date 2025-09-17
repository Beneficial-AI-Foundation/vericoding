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
/* helper modified by LLM (iteration 4): Added missing lemmas for non-negative values and div/mod identity */
proof fn lemma_str2int_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
    // Str2Int always returns nat which is non-negative
}

proof fn lemma_div_mod_identity(dividend: nat, divisor: nat)
    requires divisor > 0
    ensures dividend == (dividend / divisor) * divisor + (dividend % divisor),
        dividend % divisor < divisor
{
    // Built-in arithmetic properties hold for nat division
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
/* code modified by LLM (iteration 4): Removed lemma calls that caused compilation errors */
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

