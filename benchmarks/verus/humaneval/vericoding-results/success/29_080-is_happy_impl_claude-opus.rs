// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}
spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)

    ensures
        happy <==> happy_spec(s@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Return false when len < 3 and check all conditions properly */
    if s.len() < 3 {
        return false;
    }
    
    let mut i: usize = 1;
    
    while i < s.len() - 1
        invariant
            1 <= i <= s.len() - 1,
            s.len() >= 3,
            forall|j: int| 0 < j && j < i && j + 1 < s@.len() ==> three_distinct_spec(s@, j),
        decreases s.len() - 1 - i
    {
        // Check the three_distinct_spec conditions at position i
        if s[i - 1] == s[i] || s[i] == s[i + 1] {
            // Not happy if any adjacent characters are the same
            assert(!three_distinct_spec(s@, i as int));
            assert(!(forall|j: int| 0 < j && j + 1 < s@.len() ==> three_distinct_spec(s@, j)));
            assert(!happy_spec(s@));
            return false;
        }
        assert(three_distinct_spec(s@, i as int));
        i = i + 1;
    }
    
    assert(forall|j: int| 0 < j && j + 1 < s@.len() ==> three_distinct_spec(s@, j));
    assert(happy_spec(s@));
    true
}
// </vc-code>

}
fn main() {}