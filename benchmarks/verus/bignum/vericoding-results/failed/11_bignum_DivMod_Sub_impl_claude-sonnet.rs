// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    str2int(s1) >= str2int(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) - str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed seq_to_vec to use proper usize casting and Vec indexing instead of Seq indexing */
exec fn bit_string_ge(s1: &Vec<char>, s2: &Vec<char>) -> (result: bool)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures result == (str2int(s1@) >= str2int(s2@))
{
  if s1.len() > s2.len() {
    return true;
  }
  if s1.len() < s2.len() {
    return false;
  }
  
  let mut i: usize = 0;
  while i < s1.len()
    invariant
      0 <= i <= s1.len(),
      s1.len() == s2.len(),
      valid_bit_string(s1@) && valid_bit_string(s2@)
  {
    if s1[i] == '1' && s2[i] == '0' {
      return true;
    }
    if s1[i] == '0' && s2[i] == '1' {
      return false;
    }
    i += 1;
  }
  true
}

exec fn seq_to_vec(s: Seq<char>) -> (result: Vec<char>)
  requires valid_bit_string(s)
  ensures result@ == s && valid_bit_string(result@)
{
  let mut result = Vec::new();
  let mut i: usize = 0;
  while i < s.len() as usize
    invariant
      0 <= i <= s.len(),
      result@.len() == i,
      result@ == s.subrange(0, i as int),
      valid_bit_string(s)
  {
    result.push(s[i as int]);
    i += 1;
  }
  result
}

spec fn str2int_zero() -> nat
{
  str2int(seq!['0'])
}

proof fn str2int_monotonic_lemma(s1: Seq<char>, s2: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > s2.len()
  ensures str2int(s1) >= str2int(s2)
{
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): Fixed type mismatch and indexing errors */
  let mut quotient = Vec::new();
  let mut remainder = dividend.clone();
  
  quotient.push('0');
  
  while remainder.len() > 0 && bit_string_ge(&remainder, &divisor)
    invariant
      valid_bit_string(quotient@) && valid_bit_string(remainder@),
      valid_bit_string(divisor@),
      str2int(divisor@) > 0,
      str2int(remainder@) + str2int(quotient@) * str2int(divisor@) == str2int(dividend@)
  {
    let sub_result = sub(remainder@, divisor@);
    remainder = seq_to_vec(sub_result);
    
    let mut new_quotient = Vec::new();
    new_quotient.push('1');
    quotient = new_quotient;
  }
  
  (quotient, remainder)
}
// </vc-code>


}

fn main() {}