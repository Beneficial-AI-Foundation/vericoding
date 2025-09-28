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
/* helper modified by LLM (iteration 5): no helpers needed */
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
    /* code modified by LLM (iteration 5): fixed indexing issues by using int for loop variable and casting for Vec access */
    let s_len: int = s.len() as int;
    let mut count: usize = 0;
    let mut i: int = 0;
    while i < s_len - 1
        invariant
            0 <= i <= s_len - 1,
            count as int == count_segments(s@.subrange(0, i + 1)) - 1,
        decreases (s_len - i)
    {
        if s@[i as usize] != s@[(i + 1) as usize] {
            count = count + 1;
        }
        i = i + 1;
    }
    count as i8
}
// </vc-code>


}

fn main() {}