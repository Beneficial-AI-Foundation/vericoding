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
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
      valid_bit_string(t) &&
      t.len() > 0 &&
      (t.len() > 1 ==> t[0] != '0') &&
      (valid_bit_string(s) ==> str2int(s) == str2int(t))
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 6): Replace while loop with recursion to fix compilation error in proof function */
proof fn normalize_bit_string_helper(s: Seq<char>) -> (t: Seq<char>)
  ensures
      valid_bit_string(t) &&
      t.len() > 0 &&
      (t.len() > 1 ==> t[0] != '0') &&
      (valid_bit_string(s) ==> str2int(s) == str2int(t))
  decreases s.len()
{
    if !valid_bit_string(s) {
        Seq::empty().push('0')
    } else if s.len() == 0 {
        Seq::empty().push('0')
    } else if s.len() == 1 {
        s
    } else {
        if s[0] == '0' {
            let t_rest = normalize_bit_string_helper(s.subrange(1, s.len() as int));
            t_rest
        } else {
            s
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i8)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
      (str2int(s1@) < str2int(s2@) ==> res as int == -1) &&
      (str2int(s1@) == str2int(s2@) ==> res as int == 0) &&
      (str2int(s1@) > str2int(s2@) ==> res as int == 1)
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): Added decreases clauses to all while loops to fix termination verification */
    let mut norm_s1 = s1;
    // Remove leading zeros, but leave at least one if the string is all zeros.
    while norm_s1.len() > 1 && norm_s1[0] == '0'
        decreases norm_s1.len()
    {
        norm_s1.remove(0);
    }

    let mut norm_s2 = s2;
    while norm_s2.len() > 1 && norm_s2[0] == '0'
        decreases norm_s2.len()
    {
        norm_s2.remove(0);
    }

    if norm_s1.len() < norm_s2.len() {
        -1i8
    } else if norm_s1.len() > norm_s2.len() {
        1i8
    } else {
        let mut i: usize = 0;
        while i < norm_s1.len()
            decreases norm_s1.len() - i
        {
            if norm_s1[i] != norm_s2[i] {
                if norm_s1[i] == '0' {
                    return -1i8;
                } else {
                    return 1i8;
                }
            }
            i += 1;
        }
        0i8
    }
}
// </vc-code>


}

fn main() {}