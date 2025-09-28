// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_vowel(c: char) -> bool {
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed assert_forall syntax by adding proper proof body structure */
spec fn filter_condition(s: Seq<char>, i: int) -> bool {
    0 <= i < s.len() && i % 2 == 0 && is_upper_vowel(s[i])
}

proof fn set_len_equal(s: Seq<char>)
    ensures
        Set::<int>::new(|i: int| filter_condition(s, i)).len() == seq![int]().filter(|i| filter_condition(s, i)).len(),
{
    let filtered_set = Set::<int>::new(|i: int| filter_condition(s, i));
    let filtered_seq = seq![int]().filter(|i| filter_condition(s, i));
    
    assert forall|i: int| filter_condition(s, i) implies i in filtered_set {
        assert(filtered_set.contains(i));
    }
    
    assert forall|i: int| i in filtered_set implies filter_condition(s, i) {
        assert(filtered_set.contains(i) ==> filter_condition(s, i));
    }
}

proof fn lemma_index_lte_len<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] == s.index(i),
{
}

// </vc-helpers>

// <vc-spec>
fn count_upper(s: Vec<char>) -> (cnt: usize)
    ensures cnt == Set::<int>::new(|i: int| 0 <= i < s@.len() && i % 2 == 0 && is_upper_vowel(s@[i])).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified and kept basic counting logic */
    let mut cnt: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            cnt == Set::<int>::new(|j: int| 0 <= j < i as int && j % 2 == 0 && is_upper_vowel(s@[j])).len(),
            i <= s.len(),
        decreases s.len() - i,
    {
        if i % 2 == 0 && is_upper_vowel(s[i]) {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    
    cnt
}
// </vc-code>


}

fn main() {}