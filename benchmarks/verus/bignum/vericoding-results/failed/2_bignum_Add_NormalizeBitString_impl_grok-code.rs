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

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
spec fn bit_val(c: char) -> int {
  if c == '1' { 1 } else { 0 }
}

/* helper modified by LLM (iteration 10): removed invalid 'int' suffixes from number literals */

fn add_bits(b1: char, b2: char, carry_in: bool) -> (result: (char, bool))
  requires
    b1 == '0' || b1 == '1',
    b2 == '0' || b2 == '1',
  ensures
    result.0 == '0' || result.0 == '1',
    bit_val(result.0) == (bit_val(b1) + bit_val(b2) + if carry_in { 1 } else { 0 }) % 2,
    result.1 == ((bit_val(b1) + bit_val(b2) + if carry_in { 1 } else { 0 }) >= 2),
{
  let sum = bit_val(b1) + bit_val(b2) + if carry_in { 1 } else { 0 };
  let sum_bit = if sum % 2 == 1 { '1' } else { '0' };
  let carry_out = sum >= 2;
  (sum_bit, carry_out)
}
// </vc-helpers>

// <vc-spec>
fn add(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) + str2int(s2@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): no changes needed as errors were in helpers */
{
  let len1 = s1.len();
  let len2 = s2.len();
  let max_len = if len1 <= len2 { len2 } else { len1 };
  let mut carry = false;
  let mut res: Vec<char> = vec![];
  let mut i = 0;
  while i < max_len
    invariant
      0 <= i <= max_len,
      valid_bit_string(res@),
      i == res.len(),
      carry || !carry,
  {
    let b1 = if i < len1 { s1[len1 - 1 - i] } else { '0' };
    let b2 = if i < len2 { s2[len2 - 1 - i] } else { '0' };
    let (sum_bit, carry_out) = add_bits(b1, b2, carry);
    res.push(sum_bit);
    carry = carry_out;
    i += 1;
  }
  if carry {
    res.push('1');
  }
  res.reverse();
  res
}
// </vc-code>


}

fn main() {}