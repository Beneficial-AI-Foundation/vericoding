// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by adding 'fn' */
spec fn matches_at(s: Seq<char>, substr: Seq<char>, pos: int) -> bool {
    0 <= pos && pos + substr.len() <= s.len() && s.subrange(pos, pos + substr.len()) == substr
}

proof fn lemma_matches_at_bounds(s: Seq<char>, substr: Seq<char>, pos: int)
    ensures matches_at(s, substr, pos) ==> 0 <= pos <= s.len() - substr.len()
{
}

proof fn lemma_count_matches_correct(s: Seq<char>, substr: Seq<char>, count: usize, end: int)
    requires 0 <= end <= s.len() - substr.len() + 1,
        count == Set::new(|i: int| 0 <= i < end && matches_at(s, substr, i)).len()
    ensures count == Set::new(|i: int| 0 <= i < end && s.subrange(i, i + substr.len()) == substr).len()
{
}
// </vc-helpers>

// <vc-spec>
fn how_many_times(s: Vec<char>, substr: Vec<char>) -> (times: usize)
    ensures times == Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type error by using ghost variable declaration */
    if substr@.len() == 0nat {
        return s.len() + 1;
    }
    if substr@.len() > s@.len() {
        return 0;
    }
    
    let mut count: usize = 0;
    let mut i: usize = 0;
    let end = s.len() - substr.len() + 1;
    
    while i < end
        invariant
            0 <= i <= end,
            end == s@.len() - substr@.len() + 1,
            count == Set::new(|j: int| 0 <= j < i && matches_at(s@, substr@, j)).len()
    {
        let ghost ghost_i: int = i as int;
        if s@.subrange(ghost_i, ghost_i + substr@.len()) == substr@ {
            count = count + 1usize;
        }
        i = i + 1;
    }
    
    proof {
        assert(Set::new(|j: int| 0 <= j < i && matches_at(s@, substr@, j)) == 
               Set::new(|j: int| 0 <= j <= s@.len() - substr@.len() && s@.subrange(j, j + substr@.len()) == substr@));
    }
    
    count
}
// </vc-code>


}

fn main() {}