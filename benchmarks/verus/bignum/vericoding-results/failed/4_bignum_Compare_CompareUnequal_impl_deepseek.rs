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
/* helper modified by LLM (iteration 10): fixed type conversion from usize to int */
proof fn lemma_str2int_not_equal(a: Seq<char>, b: Seq<char>, i: int)
    requires 
        valid_bit_string(a) && valid_bit_string(b),
        0 <= i <= a.len(),
        0 <= i <= b.len(),
        forall|j: int| 0 <= j < i ==> a[j] == b[j],
        i < a.len() || i < b.len()
    ensures str2int(a) != str2int(b)
{
    if i < a.len() && i < b.len() {
        assert(a[i] != b[i]);
        let a_prefix = a.subrange(0, i);
        let b_prefix = b.subrange(0, i);
        let a_char_val = if a[i] == '1' { 1nat } else { 0nat };
        let b_char_val = if b[i] == '1' { 1nat } else { 0nat };
        
        proof {
            assert(str2int(a) == 2nat * str2int(a_prefix) + a_char_val);
            assert(str2int(b) == 2nat * str2int(b_prefix) + b_char_val);
            assert(str2int(a_prefix) == str2int(b_prefix));
            assert(a_char_val != b_char_val);
        }
    } else if i >= a.len() && i < b.len() {
        proof {
            assert(str2int(a) < 2nat.pow(i as nat));
            assert(str2int(b) >= 2nat.pow(i as nat));
        }
    } else if i >= b.len() && i < a.len() {
        proof {
            assert(str2int(b) < 2nat.pow(i as nat));
            assert(str2int(a) >= 2nat.pow(i as nat));
        }
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
{
    /* code modified by LLM (iteration 10): fixed int conversion issue */
    let len1 = s1.len();
    let len2 = s2.len();
    
    if len1 > len2 {
        return 1;
    } else if len1 < len2 {
        return -1;
    }
    
    let mut i: usize = 0;
    while i < len1
        invariant 
            0 <= i <= len1,
            forall|j: int| 0 <= j < i ==> s1@[j] == s2@[j],
            str2int(s1@.subrange(0, i as int)) == str2int(s2@.subrange(0, i as int)),
            valid_bit_string(s1@.subrange(0, i as int)),
            valid_bit_string(s2@.subrange(0, i as int))
        decreases len1 - i
    {
        assert(i < s1@.len());
        assert(i < s2@.len());
        
        if s1[i] > s2[i] {
            lemma_str2int_not_equal(s1@, s2@, i as int);
            return 1;
        } else if s1[i] < s2[i] {
            lemma_str2int_not_equal(s1@, s2@, i as int);
            return -1;
        }
        i += 1;
    }
    
    return 0;
}
// </vc-code>


}

fn main() {}