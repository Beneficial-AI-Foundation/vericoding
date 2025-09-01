use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}
// pure-end
spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}
// pure-end

// <vc-helpers>
// No additional helpers needed, but we need to fix the typo in three_distinct_spec
// The spec function three_distinct_spec in PREAMBLE has a typo that needs to be worked around
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    // post-conditions-start
    ensures
        happy <==> happy_spec(s@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if s.len() < 3 {
        return false;
    }
    
    let mut i: usize = 1;
    while i < s.len() - 1
        invariant
            1 <= i <= s.len() - 1,
            s.len() >= 3,
            forall|j: int| 0 < j && j < i as int ==> three_distinct_spec(s@, j),
        decreases s.len() - 1 - i,
    {
        assert(0 <= i - 1 < s.len());
        assert(0 <= i < s.len());
        assert(0 <= i + 1 < s.len());
        
        // Check if the three consecutive characters are all distinct
        // Note: three_distinct_spec has a typo, but we work with its actual definition
        if s[i - 1] == s[i] || s[i] == s[i + 1] {
            // If any pair is equal, then three_distinct_spec(s@, i as int) is false
            assert(!three_distinct_spec(s@, i as int));
            assert(!(forall|j: int| 0 < j && j + 1 < s@.len() ==> three_distinct_spec(s@, j)));
            assert(!happy_spec(s@));
            return false;
        }
        
        // All three are distinct (note the typo in three_distinct_spec doesn't affect correctness here)
        assert(s@[(i - 1) as int] != s@[i as int]);
        assert(s@[i as int] != s@[(i + 1) as int]);
        assert(three_distinct_spec(s@, i as int));
        i = i + 1;
    }
    
    assert(i == s.len() - 1);
    assert(forall|j: int| 0 < j && j < (s.len() - 1) as int ==> three_distinct_spec(s@, j));
    assert(forall|j: int| 0 < j && j + 1 < s@.len() ==> three_distinct_spec(s@, j));
    assert(happy_spec(s@));
    true
}
// </vc-code>

fn main() {}
}