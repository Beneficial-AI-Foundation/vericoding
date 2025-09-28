// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1 as int)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t),
{
  assume(false);
  unreached()
}

fn compare_unequal(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
    s1.len() > s2.len(),
  ensures
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1,
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed type mismatches by casting to nat for pow function */
use vstd::arithmetic::power::*;

proof fn lemma_normalized_strings_preserve_comparison(s1: Seq<char>, s2: Seq<char>, t1: Seq<char>, t2: Seq<char>)
    requires
        valid_bit_string(s1) && valid_bit_string(s2),
        valid_bit_string(t1) && valid_bit_string(t2),
        str2int(s1) == str2int(t1),
        str2int(s2) == str2int(t2)
    ensures
        str2int(s1) < str2int(s2) <==> str2int(t1) < str2int(t2),
        str2int(s1) == str2int(s2) <==> str2int(t1) == str2int(t2),
        str2int(s1) > str2int(s2) <==> str2int(t1) > str2int(t2)
{
}

proof fn lemma_longer_normalized_string_greater(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_bit_string(s1) && valid_bit_string(s2),
        s1.len() > 0 && s2.len() > 0,
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0',
        s1.len() > s2.len()
    ensures str2int(s1) > str2int(s2)
{
    if s1.len() == 1 {
        assert(s2.len() == 0);
    } else {
        assert(s1[0] != '0');
        assert(str2int(s1) >= pow(2, (s1.len() - 1) as nat));
        assert(str2int(s2) < pow(2, s2.len() as nat));
        assert(pow(2, (s1.len() - 1) as nat) >= pow(2, s2.len() as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1,
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): use @ for sequence access directly */
    let s1_seq = s1@;
    let s2_seq = s2@;
    let t1 = normalize_bit_string(s1_seq);
    let t2 = normalize_bit_string(s2_seq);
    
    proof {
        lemma_normalized_strings_preserve_comparison(s1_seq, s2_seq, t1, t2);
    }
    
    if t1.len() > t2.len() {
        proof {
            lemma_longer_normalized_string_greater(t1, t2);
        }
        1
    } else if t1.len() < t2.len() {
        proof {
            lemma_longer_normalized_string_greater(t2, t1);
        }
        -1
    } else {
        compare_unequal(t1, t2)
    }
}
// </vc-code>


}

fn main() {}