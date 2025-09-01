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
spec fn three_distinct_spec_corrected(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
}

spec fn three_distinct_equivalence(s: Seq<char>, i: int) -> (ret: bool)
    recommends 0 < i && i + 1 < s.len()
{
    three_distinct_spec(s, i) == three_distinct_spec_corrected(s, i)
}

proof fn happy_spec_equivalence(s: Seq<char>)
    ensures happy_spec(s) == (s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec_corrected(s, i)))
{
    if s.len() >= 3 {
        assert(forall|i: int| 0 < i && i + 1 < s.len() ==> 
            #[trigger] three_distinct_spec(s, i) == three_distinct_spec_corrected(s, i)) by {
            assert(forall|i: int| 0 < i && i + 1 < s.len() ==> {
                three_distinct_equivalence(s, i)
            });
        }
    }
}
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
    while i + 1 < s.len()
        invariant
            1 <= i < s.len(),
            s.len() >= 3,
            forall|j: int| 0 < j < i && j + 1 < s@.len() ==> three_distinct_spec_corrected(s@, j),
        decreases s.len() - i,
    {
        if s[i - 1] == s[i] || s[i] == s[i + 1] || s[i - 1] == s[i + 1] {
            return false;
        }
        i += 1;
    }
    
    proof {
        assert(i + 1 >= s.len());
        assert(i == s.len() - 1);
        assert(forall|j: int| 0 < j && j + 1 < s@.len() ==> three_distinct_spec_corrected(s@, j)) by {
            assert(forall|j: int| 0 < j && j + 1 < s@.len() ==> {
                assert(j < i);
                three_distinct_spec_corrected(s@, j)
            });
        }
        happy_spec_equivalence(s@);
    }
    
    true
}
// </vc-code>

fn main() {}
}