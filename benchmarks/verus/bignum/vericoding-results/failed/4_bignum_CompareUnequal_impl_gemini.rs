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
/* helper modified by LLM (iteration 10): fixed E0425 compilation errors for pow2 and lemma_mul_pow_is_pow_add */
use vstd::arithmetic::power::*;

proof fn str2int_upper_bound(s: Seq<char>)
    requires valid_bit_string(s),
    ensures str2int(s) < pow(2, s.len() as nat),
    decreases s.len(),
{
    if s.len() > 0 {
        let prefix = s.subrange(0, s.len() - 1);
        str2int_upper_bound(prefix);
        lemma_mul_is_pow_add(2, 1, prefix.len() as nat);
    }
}

proof fn str2int_lower_bound_no_leading_zeros(s: Seq<char>)
    requires
        valid_bit_string(s),
        s.len() >= 1,
        s.len() > 1 ==> s[0] != '0',
    ensures
        str2int(s) >= (if s.len() == 1 && s[0] == '0' { 0 } else { pow(2, (s.len() - 1) as nat) }),
    decreases s.len(),
{
    if s.len() > 1 {
        let prefix = s.subrange(0, s.len() - 1);
        str2int_lower_bound_no_leading_zeros(prefix);
        lemma_mul_is_pow_add(2, 1, (s.len() - 2) as nat);
    }
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
    /* code modified by LLM (iteration 10): fixed compilation errors by using correct function names */
    proof {
        str2int_lower_bound_no_leading_zeros(s1@);
        str2int_upper_bound(s2@);

        assert(s1@.len() > s2@.len());
        assert(s2@.len() > 0);
        assert(s1@.len() >= 2);

        assert(str2int(s1@) >= pow(2, (s1@.len() - 1) as nat));
        assert(str2int(s2@) < pow(2, s2@.len() as nat));

        assert((s1@.len() - 1) as nat >= s2@.len() as nat);
        lemma_pow_increases(2, s2@.len() as nat, (s1@.len() - 1) as nat);
        
        assert(pow(2, (s1@.len() - 1) as nat) >= pow(2, s2@.len() as nat));
        assert(str2int(s1@) >= pow(2, s2@.len() as nat));

        assert(str2int(s1@) > str2int(s2@));
    }
    1
}
// </vc-code>


}

fn main() {}