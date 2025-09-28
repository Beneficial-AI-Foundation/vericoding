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
/* helper modified by LLM (iteration 10): Removed unnecessary `(len1_nat - 1) as nat` and similar `as nat` casts as `len1_nat` and `len2_nat` are already `nat` types. This resolves the `mismatched types` error (`expected nat, found int`), as the `pow` function expects `nat` for its exponent. */
use vstd::arithmetic::power::pow;

proof fn lemma_str2int_ge_0(s: Seq<char>)
  requires
    valid_bit_string(s)
  ensures
    str2int(s) >= 0
{
}

proof fn lemma_str2int_len_gt_implies_greater(s1: Seq<char>, s2: Seq<char>)
  requires
    valid_bit_string(s1),
    valid_bit_string(s2),
    s1.len() > s2.len(),
    s1.len() > 0,
    s2.len() > 0,
    s1[0] == '1' // s1 must not be '0' followed by other digits
  ensures
    str2int(s1) > str2int(s2)
  decreases s1.len()
{
  if s2.len() == 0 {
    // This case is actually impossible due to requires s2.len() > 0
    // The `assert(false)` is not needed because the verifier will see this path is unreachable
  } else {
    // Smallest s1.len() is 2 (since s1.len() > s2.len() >= 1)
    // The `s1[0] == '1'` implies str2int(s1) >= 2^(s1.len() - 1).
    // The maximum value for str2int(s2) is 2^(s2.len()) - 1.
    // Since s1.len() > s2.len(), this leads to str2int(s1) > str2int(s2)
    lemma_str2int_ge_0(s2);

    if s1.len() == (s2.len() as int) + 1 {
      // Base case for length difference of 1
      // str2int(s1) >= 2^(s1.len() - 1) due to s1[0] == '1'
      // str2int(s2) <= 2^(s2.len()) - 1
      let len1_nat = s1.len() as nat;
      let len2_nat = s2.len() as nat;

      assert(str2int(s1) >= pow(2, len1_nat - 1));
      assert(pow(2, len2_nat) > str2int(s2));
      assert(len1_nat - 1 == len2_nat);
      assert(pow(2, len2_nat) > pow(2, len2_nat) - 1); // trivial, but ensures context
      assert(pow(2, len1_nat - 1) > pow(2, len2_nat) - 1);
      assert(str2int(s1) > str2int(s2));
    } else {
      // Inductive step: s1.len() > s2.len() + 1
      let s1_prefix = s1.subrange(0, s1.len() - 1);
      lemma_str2int_ge_0(s1_prefix);
      
      // s1_prefix.len() = s1.len() - 1. Since s1.len() > s2.len() + 1, then s1_prefix.len() > s2.len().
      // s1_prefix[0] == s1[0] == '1' is not necessarily true if s1[0] == '0' was allowed
      // but here s1[0] == '1' is a precise requirement
      assert(s1_prefix.len() > s2.len());
      assert(s1_prefix.len() > 0);
      // The specification requires s1[0] != '0' for s1.len() > 1. Here, s1_prefix.len() >= 1.
      // If s1_prefix.len() > 0, then s1_prefix[0] exists. s1_prefix[0] == s1[0].
      // If s1_prefix.len() == 1, then s1[0] == '1'.
      // If s1_prefix.len() > 1, then s1_prefix[0] == s1[0] == '1'.
      // So, s1_prefix[0] == '1' holds.
      if s1_prefix.len() > 1 {
        assert(s1_prefix[0] == '1');
      } else if s1_prefix.len() == 1 {
        assert(s1_prefix[0] == s1[0]); // s1[0] is '1' by invariant
        assert(s1_prefix[0] == '1');
      }
      
      lemma_str2int_len_gt_implies_greater(s1_prefix, s2);
      assert(str2int(s1_prefix) > str2int(s2));
      
      // str2int(s1) = 2 * str2int(s1_prefix) + (0 or 1)
      // Since str2int(s1_prefix) > str2int(s2) and str2int(s1_prefix) >= 1 (because s1_prefix[0] == '1' and s1_prefix.len() > 0),
      // then 2 * str2int(s1_prefix) >= 2 * (str2int(s2) + 1) = 2 * str2int(s2) + 2.
      // Therefore, 2 * str2int(s1_prefix) > str2int(s2).
      assert(str2int(s1_prefix) >= 1nat); // because s1_prefix[0] == '1' and s1_prefix.len() > 0. If s1_prefix is "1", str2int is 1.
      assert(str2int(s1_prefix) >= str2int(s2) + 1);
      assert(2 * str2int(s1_prefix) >= 2 * (str2int(s2) + 1));
      assert(2 * str2int(s1_prefix) >= 2 * str2int(s2) + 2);
      assert(str2int(s1) >= 2 * str2int(s1_prefix));
      assert(str2int(s1) >= 2 * str2int(s2) + 2);
      assert(str2int(s1) > str2int(s2));
    }
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
/* code modified by LLM (iteration 10): No changes needed in this section as the previous fix was accurate and the compilation error was in the helper section. */
{
    proof {
        lemma_str2int_len_gt_implies_greater(s1@, s2@);
    }
    1
}
// </vc-code>


}

fn main() {}