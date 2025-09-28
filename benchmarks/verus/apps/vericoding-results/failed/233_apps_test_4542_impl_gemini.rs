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
/* helper modified by LLM (iteration 2): [made integer literals explicit] */
proof fn lemma_count_segments_extend(s: Seq<char>, i: int)
    requires
        1 <= i < s.len(),
    ensures
        count_segments(s.subrange(0, i + 1)) == count_segments(s.subrange(0, i)) + if s[i] != s[i - 1] { 1int } else { 0int },
{
    reveal(count_segments);
}

/* helper modified by LLM (iteration 2): [added lemma for upper bound on segment count] */
proof fn lemma_count_segments_le_len(s: Seq<char>)
    requires
        s.len() > 0,
    ensures
        count_segments(s) <= s.len(),
    decreases s.len()
{
    reveal(count_segments);
    if s.len() > 1 {
        lemma_count_segments_le_len(s.subrange(0, s.len() - 1));
    }
}

/* helper modified by LLM (iteration 2): [added lemma for lower bound on segment count] */
proof fn lemma_count_segments_ge_1(s: Seq<char>)
    requires
        s.len() > 0,
    ensures
        count_segments(s) >= 1,
    decreases s.len()
{
    reveal(count_segments);
    if s.len() > 1 {
        lemma_count_segments_ge_1(s.subrange(0, s.len() - 1));
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
    /* code modified by LLM (iteration 2): [fix compilation error, use lemmas for postconditions] */
    let mut count: usize = 0;
    let mut i: usize = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            count as int == count_segments(s@.subrange(0, i as int)) - 1,
        decreases s.len() - i
    {
        proof {
            lemma_count_segments_extend(s@, i as int);
        }
        if s[i] != s[i - 1] {
            count = count + 1;
        }
        i = i + 1;
    }

    proof {
        lemma_count_segments_ge_1(s@);
        lemma_count_segments_le_len(s@);
    }
    
    count as i8
}
// </vc-code>


}

fn main() {}