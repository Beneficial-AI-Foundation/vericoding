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
/* helper modified by LLM (iteration 10): Fixed ghost/exec context for sequence indexing */
proof fn str2int_normalized_equal(s: Seq<char>, t: Seq<char>)
    requires valid_bit_string(s), valid_bit_string(t), str2int(s) == str2int(t)
    ensures str2int(s) == str2int(t)
{
}

proof fn compare_normalized_strings(s1: Seq<char>, s2: Seq<char>, t1: Seq<char>, t2: Seq<char>)
    requires 
        valid_bit_string(s1),
        valid_bit_string(s2),
        valid_bit_string(t1),
        valid_bit_string(t2),
        str2int(s1) == str2int(t1),
        str2int(s2) == str2int(t2)
    ensures 
        (str2int(s1) < str2int(s2)) == (str2int(t1) < str2int(t2)),
        (str2int(s1) == str2int(s2)) == (str2int(t1) == str2int(t2)),
        (str2int(s1) > str2int(s2)) == (str2int(t1) > str2int(t2))
{
}

fn compare_normalized(t1: Seq<char>, t2: Seq<char>) -> (res: i8)
    requires 
        valid_bit_string(t1),
        valid_bit_string(t2),
        t1.len() > 0,
        t2.len() > 0,
        (t1.len() > 1 ==> t1[0] != '0'),
        (t2.len() > 1 ==> t2[0] != '0')
    ensures 
        (str2int(t1) < str2int(t2) ==> res as int == -1),
        (str2int(t1) == str2int(t2) ==> res as int == 0),
        (str2int(t1) > str2int(t2) ==> res as int == 1)
{
    if t1.len() < t2.len() {
        -1
    } else if t1.len() > t2.len() {
        1
    } else {
        let mut i: usize = 0;
        while i < t1.len()
            invariant
                0 <= i <= t1.len(),
                t1.len() == t2.len(),
                forall|j: int| 0 <= j < i ==> t1[j] == t2[j]
        {
            let c1 = t1[i as int];
            let c2 = t2[i as int];
            if c1 < c2 {
                return -1;
            } else if c1 > c2 {
                return 1;
            }
            i += 1;
        }
        0
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
    /* code modified by LLM (iteration 10): Fixed ghost/exec context for sequence indexing */
    let t1 = normalize_bit_string(s1@);
    let t2 = normalize_bit_string(s2@);
    
    proof {
        compare_normalized_strings(s1@, s2@, t1, t2);
    }
    
    compare_normalized(t1, t2)
}
// </vc-code>


}

fn main() {}