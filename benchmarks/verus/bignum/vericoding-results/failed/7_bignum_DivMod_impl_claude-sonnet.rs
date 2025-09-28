// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): added decreases clause to pow2 */
spec fn pow2(n: nat) -> nat
  decreases n
{
  if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
  requires
    valid_bit_string(s1),
    valid_bit_string(s2),
    s1.len() <= s2.len(),
    s1 == s2.subrange(s2.len() - s1.len(), s2.len() as int)
  ensures str2int(s1) <= str2int(s2)
  decreases s1.len()
{
  if s1.len() == 0 {
  } else if s1.len() == s2.len() {
  } else {
    str2int_monotonic(s1, s2.subrange(0, s2.len() - 1));
  }
}

fn compare_bit_strings(a: &Vec<char>, b: &Vec<char>) -> (result: bool)
  requires
    valid_bit_string(a@),
    valid_bit_string(b@)
  ensures result == (str2int(a@) >= str2int(b@))
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
        a.len() == b.len(),
        valid_bit_string(a@),
        valid_bit_string(b@),
        forall|j: int| 0 <= j < i ==> a@[j] == b@[j]
      decreases a.len() - i
    {
      if a[i] > b[i] {
        return true;
      } else if a[i] < b[i] {
        return false;
      }
      i += 1;
    }
    true
  }
}

fn subtract_bit_strings(a: Vec<char>, b: &Vec<char>) -> (result: Vec<char>)
  requires
    valid_bit_string(a@),
    valid_bit_string(b@),
    str2int(a@) >= str2int(b@)
  ensures
    valid_bit_string(result@),
    str2int(result@) == str2int(a@) - str2int(b@)
{
  let mut result = a;
  let mut borrow = 0;
  let mut i = 0;
  
  while i < result.len()
    invariant
      0 <= i <= result.len(),
      valid_bit_string(result@),
      borrow == 0 || borrow == 1
    decreases result.len() - i
  {
    let b_digit = if i < b.len() { if b[b.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
    let a_digit = if result[result.len() - 1 - i] == '1' { 1 } else { 0 };
    
    let diff = a_digit - b_digit - borrow;
    if diff >= 0 {
      result.set(result.len() - 1 - i, if diff == 1 { '1' } else { '0' });
      borrow = 0;
    } else {
      result.set(result.len() - 1 - i, '1');
      borrow = 1;
    }
    i += 1;
  }
  
  result
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0,
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): added decreases clause to main loop */
  let mut quotient = Vec::new();
  let mut remainder = dividend.clone();
  
  quotient.push('0');
  
  while compare_bit_strings(&remainder, &divisor)
    invariant
      valid_bit_string(quotient@),
      valid_bit_string(remainder@),
      valid_bit_string(divisor@),
      str2int(divisor@) > 0
    decreases str2int(remainder@)
  {
    remainder = subtract_bit_strings(remainder, &divisor);
    
    let mut carry = 1;
    let mut i = quotient.len();
    while i > 0 && carry > 0
      invariant
        0 <= i <= quotient.len(),
        valid_bit_string(quotient@),
        carry == 0 || carry == 1
      decreases i
    {
      i -= 1;
      if quotient[i] == '0' {
        quotient.set(i, '1');
        carry = 0;
      } else {
        quotient.set(i, '0');
        carry = 1;
      }
    }
    
    if carry == 1 {
      quotient.insert(0, '1');
    }
  }
  
  (quotient, remainder)
}
// </vc-code>


}

fn main() {}