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
/* helper modified by LLM (iteration 4): added precondition v.len() <= 128 and changed count to i8 to prevent overflow */
fn count_adjacent_changes(v: Vec<char>) -> (result: i8)
    requires 
        valid_input(v@),
        v.len() <= 128,
    ensures
        result as int == count_segments(v@) - 1,
        result >= 0,
        result as int <= v.len() - 1,
{
    let mut count: i8 = 0;
    let mut i = 0;
    while i + 1 < v.len()
        invariant 
            0 <= i < v.len(),
            count as int == count_segments(v@.subrange(0, i+1)) - 1,
            count >= 0,
            count as int <= i,
        decreases v.len() - i
    {
        if v[i] != v[i+1] {
            count = count + 1;
        }
        i += 1;
    }
    count
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
/* code modified by LLM (iteration 4): added assert to ensure input length is within bounds */
{
    assert(s.len() <= 128);
    count_adjacent_changes(s)
}
// </vc-code>


}

fn main() {}