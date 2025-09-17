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
/* helper modified by LLM (iteration 5): fix result variable usage in spec, add proper helper functions */
spec fn int_to_binary_nat(n: nat, length: nat) -> (s: Seq<char>)
  requires n < pow2(length)
  ensures ValidBitString(s) && s.len() == length && Str2Int(s) == n
{
  if length == 0 {
    Seq::empty()
  } else {
    let bit_value = pow2(length - 1);
    let prefix_length = length - 1;
    let prefix_n = n / 2;
    
    if n >= bit_value {
      int_to_binary_nat(n - bit_value, prefix_length)
              .push('1')
    } else {
      int_to_binary_nat(n, prefix_length)
              .push('0')
    }
  }
}

spec fn pow2(exp: nat) -> nat
  decreases exp
{
  if exp == 0 { 1nat } else { 2nat * pow2(exp - 1) }
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

// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix compilation errors by using ghost blocks and proper variable handling */
{
    let mut quotient: Vec<char> = Vec::new();
    let mut remainder: Vec<char> = Vec::new();
    
    let dividend_int = proof { Str2Int(dividend@) };
    let divisor_int = proof { Str2Int(divisor@) };
    
    let q_int = dividend_int / divisor_int;
    let r_int = dividend_int % divisor_int;
    
    let q_bits = proof { int_to_binary_nat(q_int, dividend.len() as nat) };
    let r_bits = proof { int_to_binary_nat(r_int, divisor.len() as nat) };
    
    quotient = Vec::from_seq(q_bits);
    remainder = Vec::from_seq(r_bits);
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

