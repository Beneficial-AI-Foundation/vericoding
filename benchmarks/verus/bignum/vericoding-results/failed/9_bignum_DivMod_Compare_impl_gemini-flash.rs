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
/* helper modified by LLM (iteration 10): Cast `j` to `usize` for sequence indexing in `bin_increment`'s invariants. */
spec fn ge_bit_string(s1: Seq<char>, s2: Seq<char>) -> bool
  recommends valid_bit_string(s1) && valid_bit_string(s2)
{
  str2int(s1) >= str2int(s2)
}

fn prepend_zero(s: &Vec<char>) -> (result: Vec<char>)
  requires valid_bit_string(s@)
  ensures 
    valid_bit_string(result@),
    str2int(result@) == str2int(s@)
{
  let mut new_s = Vec::new();
  new_s.push('0');
  let mut i = 0;
  while i < s.len()
    invariant
      0 <= i as int <= s.len() as int,
      new_s.len() == i + 1,
      forall|j: int| 0 <= j < i as int ==> new_s@[j+1] == s@[j]
  {
    new_s.push(s[i]);
    i = i + 1;
  }
  new_s
}

fn bin_increment(s: &Vec<char>) -> (result: Vec<char>)
  requires valid_bit_string(s@)
  ensures
    valid_bit_string(result@),
    str2int(result@) == str2int(s@) + 1nat
{
  let mut result = s.clone();
  let mut carry = true;
  let mut i = s.len();

  while i > 0 && carry
    invariant
      0 <= i <= s.len(),
      carry ==> (forall |j: int| i as int <= j < s.len() as int ==> result@[j as usize] == '0'),
      !carry ==> (forall |j: int| i as int <= j < s.len() as int ==> result@[j as usize] == s@[j as usize]),
      valid_bit_string(result@)
  {
    i = i - 1;
    if result[i] == '0' {
      result.set(i, '1');
      carry = false;
    } else {
      result.set(i, '0');
      carry = true;
    }
  }

  if carry {
    let mut new_s = Vec::new();
    new_s.push('1');
    let mut j = 0;
    while j < result.len()
      invariant
        0 <= j as int <= result.len() as int,
        new_s.len() == j + 1,
        forall|k: int| 0 <= k < j as int ==> new_s@[k+1] == result@[k]
    {
      new_s.push(result[j]);
      j = j + 1;
    }
    new_s
  } else {
    result
  }
}

fn vec_of_char_from_str(s: &str) -> (result: Vec<char>)
  ensures valid_bit_string(result@)
{
  let mut v = Vec::new();
  for c in s.chars() {
    v.push(c);
  }
  v
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
/* code modified by LLM (iteration 10): Handle the `divisor` being an integer type instead of `nat` in the unreachable assertion. */
{
  let zero_vec = Vec::new();
  if str2int(divisor@) == (0nat as nat) {
    unreachable!();
  }

  if str2int(dividend@) < str2int(divisor@) {
    return (vec_of_char_from_str("0"), dividend);
  }

  let mut quotient = vec_of_char_from_str("0");
  let mut remainder = vec_of_char_from_str("0");
  let mut i = 0usize;
  while i < dividend.len()
    invariant
      0 <= i && i <= dividend.len(),
      valid_bit_string(quotient@),
      valid_bit_string(remainder@),
      str2int(remainder@) < str2int(divisor@)
  {
    let mut new_remainder_vec = remainder.clone();
    new_remainder_vec.push(dividend[i]);
    let new_remainder = new_remainder_vec@;

    if ge_bit_string(new_remainder, divisor@) {
      quotient = bin_increment(&quotient);
      let mut temp_rem_vec = new_remainder_vec.clone();
      let mut j = divisor.len();
      while j > 0
        invariant
          0 <= j && j <= divisor.len(),
          valid_bit_string(temp_rem_vec@),
          valid_bit_string(divisor@)
      {
        j = j - 1;
        if temp_rem_vec[j] == '0' && divisor[j] == '1' {
          temp_rem_vec.set(j, '1');
          let mut k = j;
          while k > 0 {
            k = k - 1;
            if temp_rem_vec[k] == '1' {
              temp_rem_vec.set(k, '0');
              break;
            } else {
              temp_rem_vec.set(k, '1');
            }
          }
        } else if temp_rem_vec[j] == '1' && divisor[j] == '0' {
          temp_rem_vec.set(j, '1');
        } else {
          temp_rem_vec.set(j, '0');
        }
      }
      remainder = temp_rem_vec;
    } else {
      remainder = new_remainder_vec;
    }
    i = i + 1;
  }

  let mut final_quotient = Vec::new();
  let mut leading_zeros_q = true;
  for k in 0..quotient.len() {
    if quotient[k] == '1' {
      leading_zeros_q = false;
    }
    if !leading_zeros_q {
      final_quotient.push(quotient[k]);
    }
  }
  if final_quotient.len() == 0 {
    final_quotient.push('0');
  }

  let mut final_remainder = Vec::new();
  let mut leading_zeros_r = true;
  for k in 0..remainder.len() {
    if remainder[k] == '1' {
      leading_zeros_r = false;
    }
    if !leading_zeros_r {
      final_remainder.push(remainder[k]);
    }
  }
  if final_remainder.len() == 0 {
    final_remainder.push('0');
  }

  let result = (final_quotient, final_remainder);
  result
}
// </vc-code>


}

fn main() {}