// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
predicate! matches_at_index(s: Seq<char>, substr: Seq<char>, i: int) -> bool {
    0 <= i && i <= s.len() - substr.len() && s.subrange(i, i + substr.len()) == substr
}

proof fn lemma_subrange_length_equal<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i <= s1.len() - s2.len(),
        s1.subrange(i, i + s2.len()) == s2,
    ensures
        exists|j: int| 0 <= j <= s1.len() - s2.len() && s1.subrange(j, j + s2.len()) == s2,
{
}
// </vc-helpers>

// <vc-spec>
fn how_many_times(s: Vec<char>, substr: Vec<char>) -> (times: usize)
    ensures times == Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error with proper predicate syntax */
    let mut times: usize = 0;
    let mut i: usize = 0;
    
    while i <= s.len() - substr.len()
        invariant
            times == Set::new(|j: int| 0 <= j < i as int && matches_at_index(s@, substr@, j)).len(),
            i <= s.len() - substr.len() + 1,
        decreases s.len() - substr.len() - i,
    {
        if s[i..i + substr.len()] == substr {
            proof {
                lemma_subrange_length_equal(s@, substr@, i as int);
            }
            times = times + 1;
        }
        i = i + 1;
    }
    
    times
}
// </vc-code>


}

fn main() {}