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
/* helper modified by LLM (iteration 7): added preconditions and loop invariant for equal length case */
fn compare(a: &Vec<char>, b: &Vec<char>) -> (result: i8)
  requires 
    valid_bit_string(a@) && valid_bit_string(b@)
  ensures 
    result == -1 ==> str2int(a@) < str2int(b@),
    result == 0 ==> str2int(a@) == str2int(b@),
    result == 1 ==> str2int(a@) > str2int(b@)
{
  if a.len() > b.len() {
    return 1;
  } else if a.len() < b.len() {
    return -1;
  } else {
    for i in 0..a.len()
      invariant 
        0 <= i <= a.len(),
        a.len() == b.len(),
        forall|j: int| 0 <= j < i ==> a[j] == b[j]
    {
      if a[i] != b[i] {
        if a[i] > b[i] {
          return 1;
        } else {
          return -1;
        }
      }
    }
    return 0;
  }
}

/* helper modified by LLM (iteration 7): added preconditions and fixed j computation to avoid underflow */
fn subtract(a: &Vec<char>, b: &Vec<char>) -> (result: Vec<char>)
  requires 
    valid_bit_string(a@) && valid_bit_string(b@),
    str2int(a@) >= str2int(b@)
  ensures 
    str2int(result@) == str2int(a@) - str2int(b@),
    valid_bit_string(result@)
{
  let mut result = Vec::new();
  let mut borrow = 0;

  for forward_index in 0..a.len() {
      let i = a.len() - 1 - forward_index;
      let bit_a = if a[i] == '1' { 1 } else { 0 };
      // Fixed computation of j to avoid underflow
      let j = b.len() - 1 - forward_index;
      let bit_b = if j >= 0 && j < b.len() {
          if b[j] == '1' { 1 } else { 0 }
      } else {
          0
      };

      let total = bit_a - bit_b - borrow;
      if total < 0 {
          let bit = (total + 2) % 2;
          result.push(if bit == 1 { '1' } else { '0' });
          borrow = 1;
      } else {
          result.push(if total == 1 { '1' } else { '0' });
          borrow = 0;
      }
  }

  while result.len() > 1 && result[result.len()-1] == '0'
      decreases result.len()
  {
      result.pop();
  }

  let mut final_result = Vec::new();
  for forward_index in 0..result.len() {
      let i = result.len() - 1 - forward_index;
      final_result.push(result[i]);
  }

  final_result
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
  /* code modified by LLM (iteration 7): added loop invariants for valid_bit_string */
  let mut quotient = Vec::new();
  let mut remainder = Vec::new();

  for i in 0..dividend.len()
      invariant 
        0 <= i <= dividend.len(),
        valid_bit_string(remainder@),
        valid_bit_string(quotient@)
  {
      remainder.push(dividend[i]);
      let cmp = compare(&remainder, &divisor);
      if cmp >= 0 {
          remainder = subtract(&remainder, &divisor);
          quotient.push('1');
      } else {
          quotient.push('0');
      }
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


}

fn main() {}