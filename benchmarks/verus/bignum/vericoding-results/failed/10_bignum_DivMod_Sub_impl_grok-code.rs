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
/* helper modified by LLM (iteration 7): fixed for loop syntax to single invariant block, added proof fn lemma_chars_to_u64_equals_str2int to prove equivalence between chars_to_u64 and str2int */
spec fn int2str(n: u64) -> Seq<char>
  decreases n as int
{
  if n == 0 {
    seq!['0']
  } else if n == 1 {
    seq!['1']
  } else {
    int2str(n / 2) + seq![if n % 2 == 0 { '0' } else { '1' }]
  }
}

proof fn lemma_str2int_int2str_inverse(n: u64)
  ensures str2int(int2str(n)) == n as nat
  decreases n
{
  lemma_int2str_valid(n);
  if n == 0 {
  } else if n == 1 {
  } else {
    lemma_str2int_int2str_inverse(n / 2);
  }
}

proof fn lemma_int2str_valid(n: u64)
  ensures valid_bit_string(int2str(n))
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    lemma_int2str_valid(n / 2);
  }
}

fn chars_to_u64(s: &[char]) -> u64
  requires
    forall|i| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1',
    s.len() <= 64
{
  let mut value = 0u64;
  for i in 0..s.len()
    invariant
      i <= s.len(),
      value as nat < 2nat ^ i
  {
    value = value * 2 + if s[i] == '1' { 1u64 } else { 0u64 };
    assert(value as nat < 2nat ^ (i + 1));
  }
  value
}

fn u64_to_chars(mut n: u64) -> Vec<char> {
  if n == 0 {
    return vec!['0'];
  }
  let mut v = Vec::new();
  while n > 0
    decreases n
  {
    let bit = if n % 2 == 1 { '1' } else { '0' };
    v.insert(0, bit);
    n /= 2;
  }
  v
}

proof fn lemma_chars_to_u64_equals_str2int(s: Seq<char>)
  requires
    valid_bit_string(s),
    s.len() <= 64
  ensures
    chars_to_u64(s) as nat == str2int(s)
  decreases s.len()
{
  if s.len() == 0 {
  } else {
    lemma_chars_to_u64_equals_str2int(s.subrange(0, s.len() - 1));
    assert(str2int(s) == 2 * str2int(s.subrange(0, s.len() - 1)) + ((if s[s.len() - 1] == '1' { 1 } else { 0 }) as nat));
    let val = chars_to_u64(s);
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
/* code modified by LLM (iteration 7): removed verification bypass assume, added call to lemma_chars_to_u64_equals_str2int to prove equivalence */
{
  let dividend_u64 = chars_to_u64(&dividend);
  let divisor_u64 = chars_to_u64(&divisor);
  let quotient_u64 = dividend_u64 / divisor_u64;
  let remainder_u64 = dividend_u64 % divisor_u64;
  let quotient_vec = u64_to_chars(quotient_u64);
  let remainder_vec = u64_to_chars(remainder_u64);
  proof {
    lemma_chars_to_u64_equals_str2int(dividend@);
    lemma_chars_to_u64_equals_str2int(divisor@);
    lemma_str2int_int2str_inverse(quotient_u64);
    lemma_str2int_int2str_inverse(remainder_u64);
  }
  (quotient_vec, remainder_vec)
}
// </vc-code>


}

fn main() {}