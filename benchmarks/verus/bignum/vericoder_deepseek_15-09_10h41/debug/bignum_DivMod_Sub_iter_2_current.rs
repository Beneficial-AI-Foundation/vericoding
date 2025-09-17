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
proof fn str2int_nonnegative(s: Seq<char>) 
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
  decreases s.len()
{
  if s.len() > 0 {
    let s_prefix = s.subrange(0, s.len() as int - 1);
    str2int_nonnegative(s_prefix);
  }
}

proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
  requires ValidBitString(s1), ValidBitString(s2), s1.len() == s2.len()
  ensures forall |i: int| 0 <= i && i < s1.len() as int ==> s1.index(i) <= s2.index(i) ==> Str2Int(s1) <= Str2Int(s2)
  decreases s1.len()
{
  if s1.len() > 0 {
    let s1_prefix = s1.subrange(0, s1.len() as int - 1);
    let s2_prefix = s2.subrange(0, s2.len() as int - 1);
    str2int_monotonic(s1_prefix, s2_prefix);
  }
}

spec fn div_mod_ensures(quotient: Seq<char>, remainder: Seq<char>, dividend: Seq<char>, divisor: Seq<char>) -> bool {
  &&& ValidBitString(quotient)
  &&& ValidBitString(remainder)
  &&& Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  &&& Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
}

/* helper modified by LLM (iteration 2): add int_to_binary helper function */
fn int_to_binary(mut n: nat, length: usize) -> Option<Vec<char>>
  requires n < pow2(length as nat)
  ensures ValidBitString(result@), result.is_some() ==> (result.unwrap()@.len() == length && Str2Int(result.unwrap()@) == n)
{
  let mut binary = Vec::with_capacity(length);
  let mut remaining = n;
  
  for i in 0..length {
    let bit_value = pow2((length - i - 1) as nat);
    if remaining >= bit_value {
      binary.push('1');
      remaining = remaining - bit_value;
    } else {
      binary.push('0');
    }
  }
  
  Some(binary)
}

spec fn pow2(exp: nat) -> nat
  decreases exp
{
  if exp == 0 { 1 } else { 2 * pow2(exp - 1) }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix compilation error by using proper binary conversion */
    let mut quotient: Vec<char> = Vec::new();
    let mut remainder: Vec<char> = Vec::new();
    
    if divisor.is_empty() {
        return (quotient, remainder);
    }
    
    let mut current_dividend = dividend.to_vec();
    
    while current_dividend.len() > 0 {
        if Str2Int(remainder@) < Str2Int(divisor@) {
            remainder.push(current_dividend[0]);
            quotient.push('0');
            current_dividend = current_dividend[1..].to_vec();
        } else {
            let remainder_int = Str2Int(remainder@) - Str2Int(divisor@);
            let binary_remainder = int_to_binary(remainder_int, remainder.len()).unwrap();
            remainder = binary_remainder;
            let last_char = quotient.pop().unwrap();
            let new_byte = if last_char == '0' { '1' } else { char::from_u32(last_char as u32 + 1).unwrap() };
            quotient.push(new_byte);
        }
    }
    
    if !quotient.is_empty() && quotient[0] == '0' {
        quotient = quotient[1..].to_vec();
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

