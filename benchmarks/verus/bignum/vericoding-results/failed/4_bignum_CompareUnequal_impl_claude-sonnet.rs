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
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fix type errors by casting to nat for pow function */
use vstd::arithmetic::power::pow;

proof fn str2int_equal_length_with_no_leading_zero(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() == s2.len(),
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0'
    ensures
        str2int(s1) >= str2int(s2)
    decreases s1.len()
{
    if s1.len() == 1 {
        assert(s1[0] == '0' || s1[0] == '1');
        assert(s2[0] == '0' || s2[0] == '1');
        assert(str2int(s1) >= 0);
        assert(str2int(s2) >= 0);
    } else {
        assert(s1[0] != '0');
        assert(s2[0] != '0');
        assert(s1[0] == '1' && s2[0] == '1');
        let s1_tail = s1.subrange(1, s1.len() as int);
        let s2_tail = s2.subrange(1, s2.len() as int);
        assert(s1_tail.len() == s2_tail.len());
        str2int_equal_length_with_no_leading_zero(s1_tail, s2_tail);
        assert(str2int(s1_tail) >= str2int(s2_tail));
        assert(str2int(s1) == str2int(s1_tail) + pow(2, (s1.len() - 1) as nat));
        assert(str2int(s2) == str2int(s2_tail) + pow(2, (s2.len() - 1) as nat));
        assert(str2int(s1) >= str2int(s2));
    }
}

proof fn str2int_monotonic_with_length(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > s2.len(),
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0'
    ensures
        str2int(s1) > str2int(s2)
{
    assert(s1.len() > s2.len());
    assert(str2int(s1) >= pow(2, (s1.len() - 1) as nat));
    assert(str2int(s2) < pow(2, s2.len() as nat));
    assert(pow(2, (s1.len() - 1) as nat) >= pow(2, s2.len() as nat));
    assert(str2int(s1) > str2int(s2));
}
// </vc-helpers>

// <vc-spec>
fn compare_unequal(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
    s1@.len() > 0,
    s1@.len() > 1 ==> s1@[0] != '0',
    s2@.len() > 0,
    s2@.len() > 1 ==> s2@[0] != '0',
    s1@.len() > s2@.len()
  ensures 
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): use corrected helper lemma to prove s1 > s2 */
    proof {
        str2int_monotonic_with_length(s1@, s2@);
        assert(str2int(s1@) > str2int(s2@));
    }
    1
}
// </vc-code>


}

fn main() {}