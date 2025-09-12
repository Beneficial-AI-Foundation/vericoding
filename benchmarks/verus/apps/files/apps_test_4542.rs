// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'B' || s[i] == 'W'
}

spec fn count_segments(s: Seq<char>) -> int
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        1int
    } else {
        count_segments(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] != s[s.len() - 2] { 1int } else { 0int })
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: &Vec<char>) -> (result: u32)
    requires 
        valid_input(s@),
    ensures 
        result >= 0,
        result == count_segments(s@) - 1,
        result <= s@.len() - 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}