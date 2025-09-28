use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// <vc-helpers>
spec fn is_upper_case_char(c: char) -> bool {
    c as int >= 65 && c as int <= 90
}

proof fn lemma_char_properties()
    ensures
        forall|c: char| is_upper_case_char(c) == is_upper_case(c),
        forall|c: char| (#[trigger] c as int) >= 0 && (#[trigger] c as int) <= 0x10FFFF,
{
    assert forall|c: char| is_upper_case_char(c) == is_upper_case(c) by {
        assert(is_upper_case_char(c) == is_upper_case(c));
    };
    assert forall|c: char| (#[trigger] c as int) >= 0 && (#[trigger] c as int) <= 0x10FFFF by {
        assert(0 <= c as int <= 0x10FFFF);
    };
}

spec fn filter_count(s: Seq<char>, f: spec_fn(char) -> bool) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        let count_rest = filter_count(s.subrange(1, s.len()), f);
        if f(s[0]) {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

proof fn lemma_filter_equivalence(s: Seq<char>)
    ensures
        s.filter(|c: char| is_upper_case(c)).len() == filter_count(s, |c: char| is_upper_case(c)),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_filter_equivalence(s.subrange(1, s.len()));
    }
}

spec fn chars_seq(s: &str) -> Seq<char> {
    s@
}

proof fn lemma_seq_subrange_len<T>(s: Seq<T>, from: int, to: int)
    requires
        0 <= from <= to <= s.len(),
    ensures
        s.subrange(from, to).len() == to - from,
{
}

proof fn lemma_index_bounds<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        i as nat < s.len(),
{
}
// </vc-helpers>

// <vc-spec>
fn count_uppercase(s: &str) -> (count: usize)
    ensures 
        count >= 0,
        count as int == s@.filter(|c: char| is_upper_case(c)).len(),
// </vc-spec>
// <vc-code>
{
    lemma_char_properties();
    let mut count: usize = 0;
    let char_seq = chars_seq(s);
    let mut idx: int = 0;
    
    while idx < char_seq.len()
        invariant
            0 <= idx <= char_seq.len(),
            count as int == filter_count(char_seq.subrange(0, idx), |c: char| is_upper_case(c)),
    {
        proof {
            lemma_index_bounds(char_seq, idx);
        }
        let character = char_seq[idx];
        if is_upper_case_char(character) {
            count = count + 1;
        }
        proof {
            lemma_filter_equivalence(char_seq.subrange(0, idx));
            lemma_seq_subrange_len(char_seq, 0, idx);
        }
        idx = idx + 1;
    }
    
    proof {
        lemma_filter_equivalence(char_seq);
        assert(char_seq.subrange(0, char_seq.len()) =~= char_seq);
    }
    
    count
}
// </vc-code>

fn main() {}

}