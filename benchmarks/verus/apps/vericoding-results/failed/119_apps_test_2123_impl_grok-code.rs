// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n
}

spec fn max_in_seq(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    via max_in_seq_decreases
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail = s.subrange(1, s.len() as int);
        let tail_max = max_in_seq(tail);
        if s[0] >= tail_max { s[0] } else { tail_max }
    }
}

#[via_fn]
proof fn max_in_seq_decreases(s: Seq<int>) {
    assume(false);
}

spec fn valid_result(n: int, heights: Seq<int>, result: int) -> bool
    recommends valid_input(n, heights)
{
    result == max_in_seq(heights) &&
    forall|i: int| 0 <= i < heights.len() ==> heights[i] <= result &&
    exists|i: int| 0 <= i < heights.len() && heights[i] == result
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed the decreases proof for max_in_seq */
#[via_fn]
proof fn max_in_seq_decreases(s: Seq<int>) 
{
    if s.len() > 1 {
        let tail = s.subrange(1, s.len() as int);
        assert(tail.len() == s.len() - 1);
        assert(tail.len() < s.len());
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, heights@.map(|i, x: i8| x as int))
    ensures valid_result(n as int, heights@.map(|i, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implementing the solve method with correct loop */
    proof { reveal(max_in_seq); }
    let mut max_val = heights[0];
    let mut i = 1;
    while i < heights.len()
        invariant
            1 <= i && i as int <= heights@.len(),
            max_val as int == max_in_seq(heights@.map(|_, x: i8| x as int).subrange(0, i as int)),
        decreases heights@.len() - i as int
    {
        if heights[i] > max_val {
            max_val = heights[i];
        }
        i += 1;
    }
    max_val
}
// </vc-code>


}

fn main() {}