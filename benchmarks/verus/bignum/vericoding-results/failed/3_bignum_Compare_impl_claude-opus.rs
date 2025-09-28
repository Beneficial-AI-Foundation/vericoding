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
/* helper modified by LLM (iteration 7): Added lemmas for str2int properties with non-zero bit strings */
spec fn count_ones(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        count_ones(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

proof fn lemma_str2int_zero(s: Seq<char>)
    requires
        valid_bit_string(s),
    ensures
        str2int(s) == 0nat <==> forall|k: int| 0 <= k < s.len() ==> s[k] == '0',
    decreases s.len()
{
    if s.len() == 0 {
        assert(str2int(s) == 0nat);
    } else {
        if str2int(s) == 0nat {
            assert(str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
            assert(str2int(s.subrange(0, s.len() - 1)) == 0nat);
            assert(s[s.len() - 1] == '0');
            lemma_str2int_zero(s.subrange(0, s.len() - 1));
        }
        if forall|k: int| 0 <= k < s.len() ==> s[k] == '0' {
            assert(s[s.len() - 1] == '0');
            lemma_str2int_zero(s.subrange(0, s.len() - 1));
            assert(str2int(s.subrange(0, s.len() - 1)) == 0nat);
            assert(str2int(s) == 0nat);
        }
    }
}

proof fn lemma_str2int_nonzero(s: Seq<char>, j: int)
    requires
        valid_bit_string(s),
        0 <= j < s.len(),
        s[j] == '1',
    ensures
        str2int(s) > 0nat,
    decreases s.len()
{
    if s.len() == 1 {
        assert(j == 0);
        assert(s[0] == '1');
        assert(str2int(s) == 1nat);
    } else if j == s.len() - 1 {
        assert(s[s.len() - 1] == '1');
        assert(str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + 1nat);
        assert(str2int(s) >= 1nat);
    } else {
        assert(j < s.len() - 1);
        lemma_str2int_nonzero(s.subrange(0, s.len() - 1), j);
        assert(str2int(s.subrange(0, s.len() - 1)) > 0nat);
        assert(str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
        assert(str2int(s) >= 2nat * str2int(s.subrange(0, s.len() - 1)));
        assert(str2int(s) > 0nat);
    }
}

fn compare_impl(s1: &Vec<char>, s2: &Vec<char>, i: usize) -> (res: i32)
    requires
        valid_bit_string(s1@),
        valid_bit_string(s2@),
        0 <= i <= s1.len(),
        0 <= i <= s2.len(),
        forall|k: int| 0 <= k < i ==> s1@[k] == s2@[k],
    ensures
        res == -1 || res == 0 || res == 1,
        (i <= s1@.len() && i <= s2@.len()) ==> (
            (str2int(s1@.subrange(i as int, s1@.len() as int)) < str2int(s2@.subrange(i as int, s2@.len() as int))) ==> (res == -1)
        ),
        (i <= s1@.len() && i <= s2@.len()) ==> (
            (str2int(s1@.subrange(i as int, s1@.len() as int)) == str2int(s2@.subrange(i as int, s2@.len() as int))) ==> (res == 0)
        ),
        (i <= s1@.len() && i <= s2@.len()) ==> (
            (str2int(s1@.subrange(i as int, s1@.len() as int)) > str2int(s2@.subrange(i as int, s2@.len() as int))) ==> (res == 1)
        ),
    decreases s1.len() - i + s2.len() - i
{
    if i == s1.len() && i == s2.len() {
        proof {
            assert(s1@.subrange(i as int, s1@.len() as int).len() == 0);
            assert(s2@.subrange(i as int, s2@.len() as int).len() == 0);
            assert(str2int(s1@.subrange(i as int, s1@.len() as int)) == 0nat);
            assert(str2int(s2@.subrange(i as int, s2@.len() as int)) == 0nat);
        }
        0
    } else if i == s1.len() {
        proof {
            assert(s1@.subrange(i as int, s1@.len() as int).len() == 0);
            assert(str2int(s1@.subrange(i as int, s1@.len() as int)) == 0nat);
            assert(i < s2@.len());
        }
        let mut j = i;
        while j < s2.len()
            invariant
                i <= j <= s2.len(),
                forall|k: int| i <= k < j ==> s2@[k] == '0',
            decreases s2.len() - j
        {
            if s2[j] == '1' {
                proof {
                    lemma_str2int_nonzero(s2@.subrange(i as int, s2@.len() as int), j - i);
                }
                return -1;
            }
            j = j + 1;
        }
        proof {
            assert(forall|k: int| i <= k < s2@.len() ==> s2@[k] == '0');
            lemma_str2int_zero(s2@.subrange(i as int, s2@.len() as int));
        }
        0
    } else if i == s2.len() {
        proof {
            assert(s2@.subrange(i as int, s2@.len() as int).len() == 0);
            assert(str2int(s2@.subrange(i as int, s2@.len() as int)) == 0nat);
            assert(i < s1@.len());
        }
        let mut j = i;
        while j < s1.len()
            invariant
                i <= j <= s1.len(),
                forall|k: int| i <= k < j ==> s1@[k] == '0',
            decreases s1.len() - j
        {
            if s1[j] == '1' {
                proof {
                    lemma_str2int_nonzero(s1@.subrange(i as int, s1@.len() as int), j - i);
                }
                return 1;
            }
            j = j + 1;
        }
        proof {
            assert(forall|k: int| i <= k < s1@.len() ==> s1@[k] == '0');
            lemma_str2int_zero(s1@.subrange(i as int, s1@.len() as int));
        }
        0
    } else if s1[i] == s2[i] {
        proof {
            assert(forall|k: int| 0 <= k < i + 1 ==> s1@[k] == s2@[k]);
        }
        compare_impl(s1, s2, i + 1)
    } else if s1[i] == '0' && s2[i] == '1' {
        proof {
            let s1_sub = s1@.subrange(i as int, s1@.len() as int);
            let s2_sub = s2@.subrange(i as int, s2@.len() as int);
            assert(s1_sub[0] == '0');
            assert(s2_sub[0] == '1');
            lemma_str2int_nonzero(s2_sub, 0);
        }
        -1
    } else {
        proof {
            assert(s1@[i as int] == '1' && s2@[i as int] == '0');
            let s1_sub = s1@.subrange(i as int, s1@.len() as int);
            let s2_sub = s2@.subrange(i as int, s2@.len() as int);
            assert(s1_sub[0] == '1');
            assert(s2_sub[0] == '0');
            lemma_str2int_nonzero(s1_sub, 0);
        }
        1
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
    /* code modified by LLM (iteration 7): No changes needed in main code */
    let result = compare_impl(&s1, &s2, 0);
    proof {
        assert(forall|k: int| 0 <= k < 0 ==> s1@[k] == s2@[k]);
        assert(s1@.subrange(0, s1@.len() as int) == s1@);
        assert(s2@.subrange(0, s2@.len() as int) == s2@);
    }
    result
}
// </vc-code>


}

fn main() {}