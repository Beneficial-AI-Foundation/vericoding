// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'B' || s[i] == 'W'
}

spec fn count_segments(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() <= 1 {
        1int
    } else {
        count_segments(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] != s[s.len() - 2] { 1int } else { 0int })
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn count_segments_iterative(s: Seq<char>, i: int) -> int
    decreases i,
{
    if i <= 1 {
        1int
    } else {
        let prev = count_segments_iterative(s, i - 1);
        if i <= s.len() && s[i - 1] != s[i - 2] {
            prev + 1
        } else {
            prev
        }
    }
}

/* helper modified by LLM (iteration 5): Fixed lemma syntax */
proof fn count_segments_bounds(s: Seq<char>)
    requires valid_input(s),
    ensures count_segments(s) >= 1,
    ensures count_segments(s) <= s.len(),
    ensures count_segments(s) - 1 >= 0,
    ensures count_segments(s) - 1 <= s.len() - 1,
    decreases s.len(),
{
    if s.len() > 1 {
        count_segments_bounds(s.subrange(0, s.len() - 1));
    }
}

proof fn count_segments_iterative_equiv(s: Seq<char>, i: int)
    requires valid_input(s),
    requires 1 <= i <= s.len(),
    ensures count_segments_iterative(s, i) == count_segments(s.subrange(0, i)),
    decreases i,
{
    if i > 1 {
        count_segments_iterative_equiv(s, i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires 
        valid_input(s@),
    ensures 
        result >= 0,
        result as int == count_segments(s@) - 1,
        result as int <= s.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed i8 overflow and bounds checking */
    if s.len() == 1 {
        return 0;
    }
    
    let mut segments: usize = 1;
    let mut i: usize = 1;
    
    proof {
        count_segments_bounds(s@);
    }
    
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            segments >= 1,
            segments <= s.len(),
            segments as int == count_segments_iterative(s@, i as int),
        decreases s.len() - i,
    {
        if s[i] != s[i - 1] {
            assert(segments < s.len());
            segments = segments + 1;
        }
        i = i + 1;
        
        proof {
            count_segments_iterative_equiv(s@, i as int);
        }
    }
    
    proof {
        assert(segments as int == count_segments(s@));
    }
    
    (segments - 1) as i8
}
// </vc-code>


}

fn main() {}