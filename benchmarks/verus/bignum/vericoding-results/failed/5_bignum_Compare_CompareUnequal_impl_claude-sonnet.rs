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
/* helper modified by LLM (iteration 10): fixed assertion by properly handling bit string recurrence and bounds */
proof fn lemma_str2int_zero_prefix(s: Seq<char>)
    requires valid_bit_string(s), s.len() > 0, s[0] == '0'
    ensures str2int(s) == str2int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.subrange(1, 1).len() == 0);
        assert(str2int(s.subrange(1, 1)) == 0);
        assert(str2int(s) == 2nat * str2int(s.subrange(0, 0)) + 0nat);
        assert(str2int(s.subrange(0, 0)) == 0);
        assert(str2int(s) == 0);
    } else {
        let prefix = s.subrange(0, s.len() - 1);
        lemma_str2int_zero_prefix(prefix);
        assert(str2int(prefix) == str2int(prefix.subrange(1, prefix.len() as int)));
        assert(prefix.subrange(1, prefix.len() as int) == s.subrange(1, s.len() - 1));
        assert(str2int(s) == 2nat * str2int(prefix) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
        let tail = s.subrange(1, s.len() as int);
        assert(tail == s.subrange(1, s.len() - 1).push(s[s.len() - 1]));
        assert(str2int(tail) == 2nat * str2int(s.subrange(1, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
    }
}

proof fn lemma_str2int_shorter_implies_smaller(s1: Seq<char>, s2: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
        s1.len() > 0 && s2.len() > 0,
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0',
        s1.len() < s2.len()
    ensures str2int(s1) < str2int(s2)
    decreases s2.len()
{
    if s1.len() == 1 {
        assert(str2int(s1) <= 1nat);
        if s2.len() == 1 {
            assert(false);
        } else {
            assert(s2[0] == '1');
            let s2_rest = s2.subrange(1, s2.len() as int);
            assert(str2int(s2) == 2nat * str2int(s2.subrange(0, s2.len() - 1)) + (if s2[s2.len() - 1] == '1' { 1nat } else { 0nat }));
            assert(str2int(s2.subrange(0, s2.len() - 1)) >= 1nat);
            assert(str2int(s2) >= 2nat);
        }
    } else {
        assert(s2[0] == '1');
        let s2_prefix = s2.subrange(0, s2.len() - 1);
        if s1.len() < s2_prefix.len() {
            lemma_str2int_shorter_implies_smaller(s1, s2_prefix);
        } else {
            assert(s1.len() == s2_prefix.len());
            assert(s1[0] == '1');
            assert(str2int(s1) >= 1nat);
        }
        assert(str2int(s2) >= 2nat * str2int(s2_prefix));
        assert(str2int(s1) < str2int(s2));
    }
}

proof fn lemma_bit_string_compare_by_position(s1: Seq<char>, s2: Seq<char>, pos: int)
    requires
        valid_bit_string(s1) && valid_bit_string(s2),
        s1.len() == s2.len(),
        0 <= pos < s1.len(),
        forall|j: int| 0 <= j < pos ==> s1[j] == s2[j],
        s1[pos] != s2[pos]
    ensures
        s1[pos] == '0' && s2[pos] == '1' ==> str2int(s1) < str2int(s2),
        s1[pos] == '1' && s2[pos] == '0' ==> str2int(s1) > str2int(s2)
{
    let diff_power = 2nat.pow((s1.len() - pos - 1) as nat);
    assert(str2int(s1) + diff_power == str2int(s2) || str2int(s2) + diff_power == str2int(s1));
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
    /* code modified by LLM (iteration 10): added helper lemma for bit comparison and fixed proof logic */
    if s1.len() == 0 && s2.len() == 0 {
        return 0;
    }
    if s1.len() == 0 {
        return -1;
    }
    if s2.len() == 0 {
        return 1;
    }
    
    let mut norm_s1 = s1;
    let mut norm_s2 = s2;
    
    while norm_s1.len() > 1 && norm_s1[0] == '0'
        invariant 
            valid_bit_string(norm_s1@),
            str2int(norm_s1@) == str2int(s1@)
        decreases norm_s1.len()
    {
        proof {
            lemma_str2int_zero_prefix(norm_s1@);
        }
        norm_s1.remove(0);
    }
    
    while norm_s2.len() > 1 && norm_s2[0] == '0'
        invariant 
            valid_bit_string(norm_s2@),
            str2int(norm_s2@) == str2int(s2@)
        decreases norm_s2.len()
    {
        proof {
            lemma_str2int_zero_prefix(norm_s2@);
        }
        norm_s2.remove(0);
    }
    
    if norm_s1.len() < norm_s2.len() {
        proof {
            assert(norm_s1.len() > 0 && norm_s2.len() > 0);
            assert(norm_s1.len() > 1 ==> norm_s1@[0] != '0');
            assert(norm_s2.len() > 1 ==> norm_s2@[0] != '0');
            lemma_str2int_shorter_implies_smaller(norm_s1@, norm_s2@);
        }
        return -1;
    }
    if norm_s1.len() > norm_s2.len() {
        proof {
            assert(norm_s1.len() > 0 && norm_s2.len() > 0);
            assert(norm_s1.len() > 1 ==> norm_s1@[0] != '0');
            assert(norm_s2.len() > 1 ==> norm_s2@[0] != '0');
            lemma_str2int_shorter_implies_smaller(norm_s2@, norm_s1@);
        }
        return 1;
    }
    
    let mut i = 0;
    while i < norm_s1.len()
        invariant 
            0 <= i <= norm_s1.len(),
            norm_s1.len() == norm_s2.len(),
            valid_bit_string(norm_s1@),
            valid_bit_string(norm_s2@),
            str2int(norm_s1@) == str2int(s1@),
            str2int(norm_s2@) == str2int(s2@),
            forall|j: int| 0 <= j < i ==> norm_s1[j] == norm_s2[j]
        decreases norm_s1.len() - i
    {
        if norm_s1[i] < norm_s2[i] {
            proof {
                lemma_bit_string_compare_by_position(norm_s1@, norm_s2@, i as int);
            }
            return -1;
        }
        if norm_s1[i] > norm_s2[i] {
            proof {
                lemma_bit_string_compare_by_position(norm_s1@, norm_s2@, i as int);
            }
            return 1;
        }
        i = i + 1;
    }
    
    0
}
// </vc-code>


}

fn main() {}