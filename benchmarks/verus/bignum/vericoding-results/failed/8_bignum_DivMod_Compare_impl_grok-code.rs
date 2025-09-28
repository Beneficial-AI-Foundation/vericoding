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
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1
  decreases str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 8): Changed recommends to requires for proof function */
proof fn str2int_spec(s: Seq<char>) -> nat
  requires valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int_spec(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string_spec(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn compare_spec(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1
{
  let len1 = s1.len();
  let len2 = s2.len();
  if len1 > len2 {
    let diff = len1 - len2;
    for i in 0..diff {
      if s1[i] == '1' { return 1; }
    }
    for i in 0..len2 {
      if s1[i + diff] == '1' && s2[i] == '0' { return 1; }
      else if s1[i + diff] == '0' && s2[i] == '1' { return -1; }
    }
    return 0;
  } else if len2 > len1 {
    let diff = len2 - len1;
    for i in 0..diff {
      if s2[i] == '1' { return -1; }
    }
    for i in 0..len1 {
      if s1[i] == '1' && s2[i + diff] == '0' { return 1; }
      else if s1[i] == '0' && s2[i + diff] == '1' { return -1; }
    }
    return 0;
  } else {
    for i in 0..len1 {
      if s1[i] == '1' && s2[i] == '0' { return 1; }
      else if s1[i] == '0' && s2[i] == '1' { return -1; }
    }
    return 0;
  }
}

/* helper modified by LLM (iteration 10): Fixed compilation error by avoiding reverse() method */
fn subtract_spec(a: Vec<char>, b: Vec<char>) -> (result: Vec<char>)
  requires
    a.len() == b.len(),
    valid_bit_string(a@),
    valid_bit_string(b@),
    str2int(a@) >= str2int(b@)
  ensures
    valid_bit_string(result@),
    result.len() == a.len(),
    str2int(result@) == str2int(a@) - str2int(b@)
{
  let mut res_vec: Vec<char> = Vec::new();
  let mut borrow: i32 = 0;
  let len = a.len();
  for i in 0..len {
    let a_bit = if a[i] == '1' { 1 } else { 0 };
    let b_bit = if b[i] == '1' { 1 } else { 0 };
    let diff = a_bit - b_bit - borrow;
    let new_bit;
    if diff < 0 {
      borrow = 1;
      new_bit = 1;
    } else {
      borrow = 0;
      new_bit = diff;
    }
    res_vec.push(if new_bit == 1 { '1' } else { '0' });
  }
  // Manual reversal to MSB first
  let mut reversed: Vec<char> = Vec::with_capacity(len);
  for i in (0..len).rev() {
    reversed.push(res_vec[i]);
  }
  reversed
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (res: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(res.0@) && valid_bit_string(res.1@),
    str2int(res.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(res.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 8): Fixed compilation issues in helpers */
  let mut quotient: Vec<char> = Vec::new();
  let mut remainder: Vec<char> = dividend;
  let dividend_len = remainder.len();
  let divisor_len = divisor.len();
  let num_shift = if dividend_len > divisor_len { dividend_len - divisor_len } else { 0 };
  for shift in 0..(num_shift + 1) {
    let shift_val = num_shift - shift;
    let mut extended_divisor: Vec<char> = Vec::new();
    for _ in 0..shift_val {
      extended_divisor.push('0');
    }
    for &ch in &divisor {
      extended_divisor.push(ch);
    }
    while extended_divisor.len() < dividend_len {
      extended_divisor.push('0');
    }
    let aligned_divisor = extended_divisor;
    if compare_spec(remainder, aligned_divisor) >= 0 {
      quotient.push('1');
      remainder = subtract_spec(remainder, aligned_divisor);
    } else {
      quotient.push('0');
    }
  }
  // Trim leading zeros for quotient
  while quotient.len() > 1 && quotient[0] == '0' {
    quotient.remove(0);
  }
  // Trim leading zeros for remainder
  while remainder.len() > 1 && remainder[0] == '0' {
    remainder.remove(0);
  }
  (quotient, remainder)
}
// </vc-code>


}

fn main() {}