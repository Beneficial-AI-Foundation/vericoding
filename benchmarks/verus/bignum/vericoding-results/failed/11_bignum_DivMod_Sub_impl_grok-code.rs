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
/* helper modified by LLM (iteration 5): Changed to use Vec<char> for executable logic, fixed type mismatches for len() and indexing */
fn compare_bit_strings(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
{
  let l1: usize = s1.len();
  let l2: usize = s2.len();
  let max_len: usize = if l1 > l2 { l1 } else { l2 };
  let mut i: usize = 0;
  while i < max_len
      invariant max_len == max_len, i <= max_len
      decreases max_len - i
  {
    let offset1: usize = if max_len > l1 { max_len - l1 } else { 0 };
    let offset2: usize = if max_len > l2 { max_len - l2 } else { 0 };
    let c1: char = if i < offset1 { '0' } else { s1[i - offset1] };
    let c2: char = if i < offset2 { '0' } else { s2[i - offset2] };
    if c1 > c2 { return 1; }
    if c2 > c1 { return -1; }
    i += 1;
  }
  return 0;
}

fn bm_sub(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(s1@) && valid_bit_string(s2@),
    str2int(s1@) >= str2int(s2@)
  ensures
    valid_bit_string(result@),
    str2int(result@) == str2int(s1@) - str2int(s2@)
{
  let l1: usize = s1.len();
  let l2: usize = s2.len();
  let max_len: usize = if l1 > l2 { l1 } else { l2 };
  let mut padded_s1: Vec<char> = Vec::new();
  for _ in 0..(max_len - l1) {
    padded_s1.push('0');
  }
  for c in s1 {
    padded_s1.push(c);
  }
  let mut padded_s2: Vec<char> = Vec::new();
  for _ in 0..(max_len - l2) {
    padded_s2.push('0');
  }
  for c in s2 {
    padded_s2.push(c);
  }
  let mut result: Vec<char> = Vec::new();
  let mut borrow: bool = false;
  let mut i: usize = max_len;
  while i > 0
      invariant
          i <= max_len,
          result.len() == max_len - i
      decreases i
  {
    i -= 1;
    let b1: u8 = if padded_s1[i] == '1' { 1 } else { 0 };
    let b2: u8 = if padded_s2[i] == '1' { 1 } else { 0 };
    let mut diff: i8 = b1 as i8 - b2 as i8 - (if borrow { 1 } else { 0 });
    borrow = diff < 0;
    if diff < 0 { diff += 2; }
    let bit: char = if diff == 1 { '1' } else { '0' };
    result.push(bit);
  }
  result.reverse();
  result
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
/* code modified by LLM (iteration 5): Used Vec<char> helpers, fixed trimmed result extraction on Vec instead of Seq to avoid ghost type issues */
{
  if dividend.len() < divisor.len() {
    return (vec!['0'], dividend);
  }
  let divisor_len: usize = divisor.len();
  let dividend_len: usize = dividend.len();
  let quotient_len: usize = dividend_len - divisor_len + 1;
  let mut quotient: Vec<char> = Vec::new();
  quotient.resize(quotient_len, '0');
  let mut remainder: Vec<char> = dividend.clone();
  let mut i: usize = quotient_len;
  while i > 0
    invariant
      0 < i <= quotient_len
    decreases i
  {
    i -= 1;
    let mut shifted: Vec<char> = divisor.clone();
    for _ in 0..i {
      shifted.push('0');
    }
    if compare_bit_strings(remainder.clone(), shifted.clone()) >= 0 {
      remainder = bm_sub(remainder.clone(), shifted.clone());
      quotient[i] = '1';
    }
  }
  let mut q_start: usize = 0;
  while q_start < quotient.len() && quotient[q_start] == '0' {
    q_start += 1;
  }
  let q_result: Vec<char> = if q_start == quotient.len() {
    vec!['0']
  } else {
    quotient[q_start..].to_vec()
  };
  let mut r_start: usize = 0;
  while r_start < remainder.len() && remainder[r_start] == '0' {
    r_start += 1;
  }
  let r_result: Vec<char> = if r_start == remainder.len() {
    vec!['0']
  } else {
    remainder[r_start..].to_vec()
  };
  proof {
    assert(str2int(q_result@) == str2int(dividend@) / str2int(divisor@));
    assert(str2int(r_result@) == str2int(dividend@) % str2int(divisor@));
  }
  (q_result, r_result)
}
// </vc-code>


}

fn main() {}