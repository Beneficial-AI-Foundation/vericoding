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
{
    if s1.len() < s2.len() {
        -1
    } else if s1.len() > s2.len() {
        1
    } else {
        let mut i = 0;
        while i < s1.len()
            invariant
                0 <= i <= s1.len(),
                valid_bit_string(s1@),
                valid_bit_string(s2@),
                s1@.len() == s2@.len(),
                forall|j: int| 0 <= j < i ==> s1@[j] == s2@[j],
            decreases s1.len() - i as int
        {
            if s1[i] < s2[i] {
                return -1;
            } else if s1[i] > s2[i] {
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