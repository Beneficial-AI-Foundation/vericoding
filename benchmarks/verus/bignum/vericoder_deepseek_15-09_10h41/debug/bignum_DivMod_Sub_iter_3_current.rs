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
/* helper modified by LLM (iteration 3): fix nat type usage in exec code and add proper helper functions */
fn int_to_binary(mut n: int, length: usize) -> Option<Vec<char>>
  requires n >= 0, n < pow2(length as nat)
  ensures result.is_some() ==> (ValidBitString(result.unwrap()@) && result.unwrap()@.len() == length && Str2Int(result.unwrap()@) == n as nat)
{
  let mut binary = Vec::with_capacity(length);
  let mut remaining = n;
  
  for i in 0..length {
    let bit_value = pow2((length - i - 1) as nat) as int;
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
    /* code modified by LLM (iteration 3): fix compilation errors and use proper binary conversion with int types */
    let mut quotient: Vec<char> = Vec::new();
    let mut remainder: Vec<char> = Vec::new();
    
    if divisor.is_empty() || Str2Int(divisor@) == 0 {
        return (quotient, remainder);
    }
    
    let dividend_int = Str2Int(dividend@) as int;
    let divisor_int = Str2Int(divisor@) as int;
    
    let q_int = dividend_int / divisor_int;
    let r_int = dividend_int % divisor_int;
    
    let q_bits = int_to_binary(q_int, dividend.len());
    let r_bits = int_to_binary(r_int, divisor.len());
    
    (q_bits.unwrap(), r_bits.unwrap())
}
// </vc-code>

fn main() {}
}

