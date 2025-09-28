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
/* helper modified by LLM (iteration 10): Changed spec fn compare_equal_len to use 'recommends' instead of 'requires' and removed 'ensures' to fix compilation error for spec functions */
fn effective_len(s: &Vec<char>) -> (len: usize)
  requires valid_bit_string(s@)
  ensures len <= s.len()
  decreases s.len()
{
  let mut i: usize = 0;
  while i < s.len()
    invariant
      0 <= i <= s.len(),
      (forall |k: int| 0 <= k < i ==> s@.index(k as int) == '0')
    decreases s.len() - i
  {
    if s[i] != '0' {
      break;
    }
    i += 1;
  }
  proof {
    assert(i <= s.len());
  }
  s.len() - i
}

spec fn compare_equal_len(s1: Seq<char>, s2: Seq<char>) -> int
    recommends
        valid_bit_string(s1) && valid_bit_string(s2),
        s1.len() == s2.len(),
        s1.len() == 0 || s1[0] == '1',
        s2.len() == 0 || s2[0] == '1'
    decreases s1.len()
{
    if s1.len() == 0 {
        0
    } else if s1[0] < s2[0] {
        -1
    } else if s1[0] > s2[0] {
        1
    } else {
        compare_equal_len(s1.subrange(1, s1.len() as int), s2.subrange(1, s2.len() as int))
    }
}
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
/* code modified by LLM (iteration 10): No changes made as the compilation error was in helpers */
{
    let eff_len1 = effective_len(&s1);
    let eff_len2 = effective_len(&s2);
    if eff_len1 > eff_len2 {
        1
    } else if eff_len1 < eff_len2 {
        -1
    } else {
        let len: usize = eff_len1;
        let start1 = s1.len() - len;
        let start2 = s2.len() - len;
        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
        {
            if s1[start1 + i] < s2[start2 + i] {
                return -1;
            } else if s1[start1 + i] > s2[start2 + i] {
                return 1;
            }
            i += 1;
        }
        0
    }
}
// </vc-code>


}

fn main() {}