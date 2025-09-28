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
/* helper modified by LLM (iteration 10): Fix type mismatches in pow2 calls */
proof fn lemma_str2int_bounds_for_comparison(s1: Seq<char>, s2: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
    s1.len() > s2.len()
  ensures str2int(s1) > str2int(s2)
{
  use vstd::arithmetic::power2::pow2;
  let len1_nat = s1.len() as nat;
  let len2_nat = s2.len() as nat;
  assert(pow2(len1_nat - 1) <= pow2(len1_nat));
  assert(pow2(len2_nat) < pow2(len1_nat));
  assert(str2int(s1) >= pow2(len1_nat - 1));
  assert(str2int(s2) < pow2(len2_nat));
  assert(pow2(len2_nat) <= pow2(len1_nat - 1));
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
    /* code modified by LLM (iteration 10): Return 1 since s1 is always greater than s2 */
    proof {
        lemma_str2int_bounds_for_comparison(s1@, s2@);
    }
    1
}
// </vc-code>


}

fn main() {}