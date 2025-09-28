// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1 as int)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
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

fn compare_unequal(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
    s1.len() > s2.len(),
  ensures
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1,
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): helper to convert ghost sequence to executable vector */
fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
  ensures v@ == s
{
  let mut result = Vec::new();
  let mut i: usize = 0;
  while i < s.len()
    invariant
      0 <= i <= s.len(),
      result.len() == i,
      result@ =~= s.subrange(0, i as int),
  {
    result.push(s[i as int]);
    i += 1;
  }
  result
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1,
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): use helper function to convert sequences to vectors */
    let ghost norm_s1_seq = normalize_bit_string(s1@);
    let ghost norm_s2_seq = normalize_bit_string(s2@);
    
    // Convert to executable vectors using helper
    let norm_s1_vec = seq_to_vec(norm_s1_seq);
    let norm_s2_vec = seq_to_vec(norm_s2_seq);
    
    if norm_s1_vec.len() == norm_s2_vec.len() {
        let mut idx = 0;
        while idx < norm_s1_vec.len()
            invariant
                0 <= idx <= norm_s1_vec.len(),
                norm_s1_vec.len() == norm_s2_vec.len(),
                forall|k: int| 0 <= k < (idx as int) ==> norm_s1_vec@[k] == norm_s2_vec@[k],
        {
            if norm_s1_vec[idx] != norm_s2_vec[idx] {
                if norm_s1_vec[idx] == '1' {
                    return 1;
                } else {
                    return -1;
                }
            }
            idx += 1;
        }
        0
    } else if norm_s1_vec.len() > norm_s2_vec.len() {
        let result = compare_unequal(norm_s1_vec@, norm_s2_vec@);
        result
    } else {
        let temp_res = compare_unequal(norm_s2_vec@, norm_s1_vec@);
        if temp_res == 1 {
            -1
        } else if temp_res == -1 {
            1
        } else {
            0
        }
    }
}
// </vc-code>


}

fn main() {}