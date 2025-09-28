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
/* helper modified by LLM (iteration 10): Fix type mismatches and indexing issues */
proof fn normalize_bit_string_helper(s: Seq<char>) -> (t: Seq<char>)
  ensures
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t),
{
  if s.len() == 0 {
    seq!['0']
  } else if s[0] == '0' {
    normalize_bit_string_helper(s.subrange(1, s.len() as int))
  } else {
    s
  }
}

proof fn compare_unequal_helper(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
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
  if s1.len() == s2.len() + 1 {
    if s1[0] == '1' && str2int(s1.subrange(1, s1.len() as int)) == str2int(s2) {
      0i32
    } else if s1[0] == '1' {
      1i32
    } else {
      -1i32
    }
  } else {
    let s1_tail = s1.subrange(1, s1.len() as int);
    compare_unequal_helper(s1_tail, s2)
  }
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
/* code modified by LLM (iteration 10): Fix type conversions and indexing */
{
    let s1_norm = normalize_bit_string_helper(s1@);
    let s2_norm = normalize_bit_string_helper(s2@);
    
    if s1_norm.len() > s2_norm.len() {
        compare_unequal_helper(s1_norm, s2_norm)
    } else if s1_norm.len() < s2_norm.len() {
        let res = compare_unequal_helper(s2_norm, s1_norm);
        if res == 1 { -1 } else if res == -1 { 1 } else { 0 }
    } else {
        let mut i: usize = 0;
        while i < s1_norm.len() as usize
            invariant
                0 <= i <= s1_norm.len() as usize,
                forall|j: int| 0 <= j < i as int ==> s1_norm[j] == s2_norm[j],
            decreases s1_norm.len() as usize - i
        {
            if s1_norm[i as int] != s2_norm[i as int] {
                if s1_norm[i as int] == '1' {
                    return 1;
                } else {
                    return -1;
                }
            }
            i += 1;
        }
        0
    }
}
// </vc-code>


}

fn main() {}