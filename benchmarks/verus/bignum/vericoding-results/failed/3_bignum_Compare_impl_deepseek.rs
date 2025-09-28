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
/* helper modified by LLM (iteration 10): fix type mismatches with proper type conversions */
use vstd::arithmetic::power2::pow2;

proof fn str2int_subrange_lemma(s: Seq<char>, start: usize, end: usize)
  requires
    valid_bit_string(s),
    start <= end <= s.len()
  ensures
    str2int(s) == str2int(s.subrange(0, start)) * pow2((s.len() as nat) - (start as nat)) + str2int(s.subrange(start, end)) * pow2((s.len() as nat) - (end as nat)) + str2int(s.subrange(end, s.len())),
    str2int(s.subrange(start, s.len())) == str2int(s.subrange(start, end)) * pow2((s.len() as nat) - (end as nat)) + str2int(s.subrange(end, s.len()))
  decreases end - start
{
  if start < end {
    let mid = start + 1;
    proof {
      str2int_subrange_lemma(s, mid, end);
    }
  }
}

proof fn str2int_nonnegative(s: Seq<char>) -> (res: nat)
  requires
    valid_bit_string(s)
  ensures
    res == str2int(s)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    let prefix = s.subrange(0, s.len() - 1);
    proof {
      str2int_nonnegative(prefix);
    }
    let val = if s[s.len() - 1] == '1' { 1nat } else { 0nat };
    2nat * str2int_nonnegative(prefix) + val
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
{
    /* code modified by LLM (iteration 10): use proper comparison by converting chars to digit values */
    let len1 = s1.len();
    let len2 = s2.len();
    
    let mut i = 0;
    while i < len1 && i < len2
        invariant
            0 <= i <= len1,
            0 <= i <= len2
    {
        let c1 = s1[i];
        let c2 = s2[i];
        
        let d1 = if c1 == '1' { 1 } else { 0 };
        let d2 = if c2 == '1' { 1 } else { 0 };
        
        if d1 < d2 {
            return -1;
        } else if d1 > d2 {
            return 1;
        }
        
        i += 1;
    }
    
    if len1 < len2 {
        -1
    } else if len1 > len2 {
        1
    } else {
        0
    }
}
// </vc-code>


}

fn main() {}