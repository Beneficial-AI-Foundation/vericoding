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
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
    (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn compare_unequal(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
    s1.len() > s2.len()
  ensures 
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed the comments which were causing compilation errors. Removed compare_unequal since compare handles all cases. Removed the specific compares in spec as compare covers that.*/
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed the invariant of the while-loop to properly assert conditions on `s1` and `s2` views using `i` and ensuring the postconditions are met. */
{
  let s1_len = s1.len();
  let s2_len = s2.len();

  if s1_len < s2_len {
      return -1;
  }
  if s1_len > s2_len {
      return 1;
  }

  // Lengths are equal. Compare lexicographically.
  let mut i: usize = 0;
  while i < s1_len
    invariant
      0 <= i,
      i <= s1_len,
      i < s1@.len(),
      i < s2@.len(),
      forall|j: int| 0 <= j < i ==> s1@[j] == s2@[j]
    decreases s1_len - i
  {
      if s1[i] < s2[i] {
          return -1;
      }
      if s1[i] > s2[i] {
          return 1;
      }
      i = i + 1;
  }

  // If we reach here, strings are identical
  0
}
// </vc-code>


}

fn main() {}