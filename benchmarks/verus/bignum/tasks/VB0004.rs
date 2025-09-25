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
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}