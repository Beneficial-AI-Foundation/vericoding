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
/* helper modified by LLM (iteration 10): Removed unused functions to simplify the solution. */
fn pad_left_with_zeros(s_vec: &mut Vec<char>, len: usize)
  requires
    valid_bit_string(s_vec@),
    len >= s_vec@.len(),
  ensures
    valid_bit_string(s_vec@),
    str2int(s_vec@) == str2int(old(s_vec@)), // Modified this line: `old` refers to the spec view, which is `Seq<char>`
    s_vec@.len() == len,
    forall |i: int| 0 <= i < len as int - old(s_vec@).len() as int ==> s_vec@[i] == '0'
{
  let s_len = s_vec.len();
  let num_zeros_to_add = (len - s_len);
  let mut i = 0;
  while i < num_zeros_to_add
    invariant
      0 <= i,
      i <= num_zeros_to_add,
      valid_bit_string(s_vec@),
      s_vec@.len() == (s_len + i) as nat,
      forall |j: int| 0 <= j < i ==> s_vec@[j] == '0'
  {
    s_vec.insert(0, '0');
    i = i + 1;
  }
}

fn remove_leading_zeros(s: &mut Vec<char>)
  requires
    valid_bit_string(s@)
  ensures
    valid_bit_string(s@),
    str2int(s@) == str2int(old(s@)),
    s@.len() == 1 ==> s@[0] == '0',
    s@.len() > 1 ==> s@[0] == '1' || str2int(s@) == 0
{
  let original_s_len = s.len();
  let mut i = 0;
  while i < s.len() - 1
    invariant
      0 <= i,
      i < original_s_len,
      valid_bit_string(s@),
      str2int(s@) == str2int(old(s@)),
      s.len() > 0
  {
    if s[0] == '0' {
      s.remove(0);
    } else {
      break;
    }
    i = i + 1;
  }
  if s.len() == 0 {
    s.push('0');
  }
}

fn sub_bit_string(s1: &mut Vec<char>, s2: &mut Vec<char>)
  requires
    valid_bit_string(s1@) && valid_bit_string(s2@),
    str2int(s1@) >= str2int(s2@),
    s1@.len() == s2@.len()
  ensures
    valid_bit_string(s1@),
    str2int(s1@) == str2int(old(s1@)) - str2int(old(s2@))
{
  let mut borrow = 0;
  let len = s1.len(); // usize
  let mut i: usize = 1; // Start from the rightmost digit
  while i <= len
    invariant
      0 <= i,
      i <= len,
      0 <= borrow <= 1,
      valid_bit_string(s1@),
      s1@.len() == len
  {
    let idx = len - i;
    let bit1 = if s1[idx] == '1' { 1 } else { 0 };
    let bit2 = if s2[idx] == '1' { 1 } else { 0 };

    let mut result_bit_val = bit1 - bit2 - borrow;
    if result_bit_val < 0 {
      result_bit_val += 2;
      borrow = 1;
    } else {
      borrow = 0;
    }
    s1[idx] = if result_bit_val == 1 { '1' } else { '0' };
    i = i + 1;
  }
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
/* code modified by LLM (iteration 10): Fixed type errors by correctly casting between usize and int for indexing and lengths. */
{
  let s_dividend = dividend@;
  let s_divisor = divisor@;

  let mut quotient_vec: Vec<char> = Vec::new();
  let mut remainder_vec: Vec<char> = Vec::new();

  if str2int(s_dividend) == 0 {
    return (vec!['0'], vec!['0']);
  }

  let mut current_remainder_vec: Vec<char> = Vec::new();
  let mut current_dividend_idx: usize = 0;

  while current_dividend_idx < s_dividend.len() as usize
    invariant
      0 <= current_dividend_idx,
      current_dividend_idx <= s_dividend.len(),
      valid_bit_string(current_remainder_vec@),
      current_remainder_vec@.len() == current_dividend_idx as nat
  {

    current_remainder_vec.push(s_dividend[current_dividend_idx as int]);
    current_dividend_idx = current_dividend_idx + 1;

    proof {
      if #[trigger]str2int(current_remainder_vec@) >= #[trigger]str2int(s_divisor) {}}
    if current_remainder_vec.len() >= (s_divisor.len() as usize) && str2int(current_remainder_vec@) >= str2int(s_divisor) {
      break;
    }
  }

  // If after taking all bits, current_remainder_vec is still less than divisor, quotient is 0
  if current_remainder_vec.len() < (s_divisor.len() as usize) || str2int(current_remainder_vec@) < str2int(s_divisor) {
    let mut final_dividend_vec = Vec::new();
    final_dividend_vec.extend_from_slice(&dividend[..]);
    remove_leading_zeros(&mut final_dividend_vec);
    return (vec!['0'], final_dividend_vec);
  }

  while current_dividend_idx <= s_dividend.len() as usize
  invariant
      0 <= current_dividend_idx,
      current_dividend_idx <= s_dividend.len(),
      valid_bit_string(current_remainder_vec@),
      valid_bit_string(quotient_vec@),
      current_remainder_vec@.len() <= s_divisor.len() + 1,
      // This invariant needs adjustment based on actual loop logic
      // For example, what is the maximum length of current_remainder_vec?
      // It can be at most s_divisor.len() + 1 (when it takes one more digit from dividend)
      // Also, ensure str2int(current_remainder_vec) - str2int(s_divisor) does not underflow
      // and it represents a valid state.
      str2int(current_remainder_vec@) < str2int(s_divisor) || current_remainder_vec.len() < s_divisor.len() + 2,
      // The below part of invariant must hold true for the current_dividend_idx after all updates in loop
      current_dividend_idx > s_dividend.len() ==> (
          (current_remainder_vec.len() >= s_divisor.len() as usize && str2int(current_remainder_vec@) >= str2int(s_divisor))
          || (current_remainder_vec.len() < s_divisor.len() as usize || str2int(current_remainder_vec@) < str2int(s_divisor))
      ),

    decreases (s_dividend.len() as int - current_dividend_idx as int)
  {
    remove_leading_zeros(&mut current_remainder_vec);

    proof {
      if #[trigger]str2int(current_remainder_vec@) >= #[trigger]str2int(s_divisor) {}
    }
    if current_remainder_vec.len() >= (s_divisor.len() as usize) && str2int(current_remainder_vec@) >= str2int(s_divisor) {
      let mut s1_for_sub_vec = current_remainder_vec.clone();
      let mut s2_for_sub_vec = divisor.clone(); // use divisor: Vec<char> directly

      let max_len = if s1_for_sub_vec.len() > s2_for_sub_vec.len() { s1_for_sub_vec.len() } else { s2_for_sub_vec.len() };

      pad_left_with_zeros(&mut s1_for_sub_vec, max_len);
      pad_left_with_zeros(&mut s2_for_sub_vec, max_len);

      proof {
        assert(s1_for_sub_vec.len() == s2_for_sub_vec.len());
        assert(valid_bit_string(s1_for_sub_vec@));
        assert(valid_bit_string(s2_for_sub_vec@));
        assert(str2int(s1_for_sub_vec@) >= str2int(s2_for_sub_vec@));
      }
      sub_bit_string(&mut s1_for_sub_vec, &mut s2_for_sub_vec);
      current_remainder_vec = s1_for_sub_vec;
      quotient_vec.push('1');
    }
    else {
      quotient_vec.push('0');
    }

    if current_dividend_idx < s_dividend.len() as usize {
      current_remainder_vec.push(s_dividend[current_dividend_idx as int]);
    }
    current_dividend_idx = current_dividend_idx + 1;
    
  }

  remove_leading_zeros(&mut quotient_vec);
  remove_leading_zeros(&mut current_remainder_vec);

  (quotient_vec, current_remainder_vec)
}
// </vc-code>


}

fn main() {}