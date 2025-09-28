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
    /* code modified by LLM (iteration 7): add trigger annotations for quantifiers */
    // Skip leading zeros in s1
    let mut start1: usize = 0;
    while start1 < s1.len() && s1[start1] == '0'
        invariant
            0 <= start1 <= s1.len(),
            forall|j: int| #[trigger] (0 <= j < start1) ==> s1[j] == '0',
        decreases s1.len() - start1
    {
        start1 = start1 + 1;
    }
    if start1 == s1.len() {
        start1 = s1.len() - 1; // Keep at least one digit
    }
    
    // Skip leading zeros in s2
    let mut start2: usize = 0;
    while start2 < s2.len() && s2[start2] == '0'
        invariant
            0 <= start2 <= s2.len(),
            forall|j: int| #[trigger] (0 <= j < start2) ==> s2[j] == '0',
        decreases s2.len() - start2
    {
        start2 = start2 + 1;
    }
    if start2 == s2.len() {
        start2 = s2.len() - 1; // Keep at least one digit
    }
    
    let len1 = s1.len() - start1;
    let len2 = s2.len() - start2;
    
    // Compare by length first
    if len1 < len2 {
        return -1;
    } else if len1 > len2 {
        return 1;
    } else {
        // Same length, compare digit by digit
        let mut i: usize = 0;
        while i < len1
            invariant
                0 <= i <= len1,
                len1 == len2,
                start1 + len1 == s1.len(),
                start2 + len2 == s2.len(),
                forall|j: int| #[trigger] (0 <= j < i) ==> s1[start1 + j] == s2[start2 + j],
            decreases len1 - i
        {
            if s1[start1 + i] < s2[start2 + i] {
                return -1;
            } else if s1[start1 + i] > s2[start2 + i] {
                return 1;
            }
            i = i + 1;
        }
        return 0;
    }
}
// </vc-code>


}

fn main() {}