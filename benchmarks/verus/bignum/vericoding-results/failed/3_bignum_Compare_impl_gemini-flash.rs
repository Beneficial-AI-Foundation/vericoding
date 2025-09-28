// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed the `i32` vs `int` type mismatch error. `i32` should be used for return type. */
spec fn compare_bit_strings_spec(s1: Seq<char>, s2: Seq<char>) -> (s: i32)
  requires
    valid_bit_string(s1),
    valid_bit_string(s2)
  ensures
    (str2int(s1) < str2int(s2)) ==> (s == -1),
    (str2int(s1) == str2int(s2)) ==> (s == 0),
    (str2int(s1) > str2int(s2)) ==> (s == 1)
{
  if str2int(s1) < str2int(s2) {
    -1
  } else if str2int(s1) == str2int(s2) {
    0
  } else {
    1
  }
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    (str2int(s1@) < str2int(s2@)) ==> (res == -1) &&
    (str2int(s1@) == str2int(s2@)) ==> (res == 0) &&
    (str2int(s1@) > str2int(s2@)) ==> (res == 1)
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Removed assumes and implemented logic to compare bit strings based on length and individual bits. */
{
  let s1_len = s1.len();
  let s2_len = s2.len();

  if s1_len < s2_len {
    return -1;
  } else if s1_len > s2_len {
    return 1;
  }

  let mut i: usize = 0;
  while i < s1_len
    invariant
      0 <= i && i <= s1_len,
      s1_len == s2_len,
      s1_len == s1@.len(),
      s2_len == s2@.len(),
      valid_bit_string(s1@),
      valid_bit_string(s2@),
      forall|k: int| 0 <= k && k < i ==> s1@[k] == s2@[k]
    decreases s1_len - i
  {
    let char1 = s1[i];
    let char2 = s2[i];
    if char1 == '0' && char2 == '1' {
      return -1;
    } else if char1 == '1' && char2 == '0' {
      return 1;
    }
    i = i + 1;
  }
  0
}
// </vc-code>


}

fn main() {}