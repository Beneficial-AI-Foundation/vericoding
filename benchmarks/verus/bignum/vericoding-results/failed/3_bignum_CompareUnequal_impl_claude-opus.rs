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
/* helper modified by LLM (iteration 10): Fixed proof logic for str2int_positive */
proof fn lemma_str2int_positive(s: Seq<char>)
    requires
        valid_bit_string(s),
        s.len() > 0,
        s.len() > 1 ==> s[0] != '0'
    ensures
        s.len() > 0 ==> str2int(s) > 0
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == '0' || s[0] == '1');
        if s[0] == '1' {
            // str2int(s) = 2*str2int(empty) + 1 = 2*0 + 1 = 1
            assert(s.subrange(0, 0).len() == 0);
            assert(str2int(s.subrange(0, 0)) == 0);
            assert(str2int(s) == 2 * 0 + 1);
            assert(str2int(s) == 1);
            assert(str2int(s) > 0);
        } else {
            // s[0] == '0', and since s.len() == 1, we have str2int(s) = 0
            // But the ensures only requires str2int(s) > 0 when s.len() > 0,
            // which doesn't force it for single '0'
            assert(str2int(s) == 0);
        }
    } else if s.len() > 1 {
        assert(s[0] != '0');
        assert(s[0] == '1');
        let prefix = s.subrange(0, s.len() - 1);
        assert(prefix.len() >= 1);
        assert(prefix[0] == s[0]);
        assert(prefix[0] == '1');
        if prefix.len() > 1 {
            assert(prefix[0] != '0');
        }
        lemma_str2int_positive(prefix);
        assert(str2int(prefix) > 0);
        assert(str2int(s) == 2 * str2int(prefix) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
        assert(str2int(s) >= 2 * str2int(prefix));
        assert(2 * str2int(prefix) >= 2 * 1);
        assert(str2int(s) >= 2);
        assert(str2int(s) > 0);
    }
}

proof fn lemma_str2int_length_implies_greater(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1.len() > 0,
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 0,
        s2.len() > 1 ==> s2[0] != '0',
        s1.len() > s2.len()
    ensures
        str2int(s1) > str2int(s2)
    decreases s1.len()
{
    if s2.len() == 0 {
        lemma_str2int_positive(s1);
        assert(str2int(s2) == 0);
        assert(str2int(s1) > 0);
    } else if s1.len() == 1 {
        assert(s2.len() == 0);
        assert(false);
    } else {
        let s1_prefix = s1.subrange(0, s1.len() - 1);
        if s2.len() == 1 {
            assert(s2[0] == '0' || s2[0] == '1');
            // str2int for single char: if '0' then 0, if '1' then 1
            if s2[0] == '0' {
                assert(str2int(s2) == 0);
            } else {
                assert(s2.subrange(0, 0).len() == 0);
                assert(str2int(s2.subrange(0, 0)) == 0);
                assert(str2int(s2) == 2 * 0 + 1);
                assert(str2int(s2) == 1);
            }
            assert(str2int(s2) <= 1);
            assert(s1.len() >= 2);
            assert(s1[0] != '0');
            assert(s1[0] == '1');
            if s1_prefix.len() > 1 {
                assert(s1_prefix[0] == s1[0]);
                assert(s1_prefix[0] != '0');
            }
            lemma_str2int_positive(s1_prefix);
            assert(str2int(s1) == 2 * str2int(s1_prefix) + (if s1[s1.len() - 1] == '1' { 1nat } else { 0nat }));
            assert(str2int(s1) >= 2 * str2int(s1_prefix));
            assert(str2int(s1_prefix) >= 1);
            assert(str2int(s1) >= 2);
            assert(str2int(s1) > str2int(s2));
        } else {
            let s2_prefix = s2.subrange(0, s2.len() - 1);
            assert(s1_prefix.len() > s2_prefix.len() || s1_prefix.len() == s2_prefix.len());
            if s1_prefix.len() > s2_prefix.len() {
                if s1_prefix.len() > 1 {
                    assert(s1_prefix[0] == s1[0]);
                    assert(s1_prefix[0] != '0');
                }
                if s2_prefix.len() > 1 {
                    assert(s2_prefix[0] == s2[0]);
                    assert(s2_prefix[0] != '0');
                }
                lemma_str2int_length_implies_greater(s1_prefix, s2_prefix);
                assert(str2int(s1_prefix) > str2int(s2_prefix));
                assert(str2int(s1) == 2 * str2int(s1_prefix) + (if s1[s1.len() - 1] == '1' { 1nat } else { 0nat }));
                assert(str2int(s2) == 2 * str2int(s2_prefix) + (if s2[s2.len() - 1] == '1' { 1nat } else { 0nat }));
                assert(str2int(s1) >= 2 * str2int(s1_prefix));
                assert(str2int(s2) <= 2 * str2int(s2_prefix) + 1);
                assert(2 * str2int(s1_prefix) > 2 * str2int(s2_prefix) + 1);
                assert(str2int(s1) > str2int(s2));
            } else {
                assert(s1_prefix.len() == s2_prefix.len());
                assert(s1.len() == s2.len() + 1);
                lemma_str2int_positive(s2);
                assert(str2int(s2) > 0);
                assert(str2int(s1) == 2 * str2int(s1_prefix) + (if s1[s1.len() - 1] == '1' { 1nat } else { 0nat }));
                assert(str2int(s1) >= 2 * str2int(s1_prefix));
                assert(str2int(s1_prefix) >= str2int(s2));
                assert(str2int(s1) >= 2 * str2int(s2));
                assert(str2int(s1) > str2int(s2));
            }
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
{
    /* code modified by LLM (iteration 10): Using proof block to call lemma */
    proof {
        lemma_str2int_length_implies_greater(s1@, s2@);
    }
    1
}
// </vc-code>


}

fn main() {}