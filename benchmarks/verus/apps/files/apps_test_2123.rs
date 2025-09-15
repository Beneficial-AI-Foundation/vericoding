// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n
}

spec fn max_in_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail_max = max_in_seq(s.subrange(1, s.len() as int));
        if s[0] >= tail_max { s[0] } else { tail_max }
    }
}

spec fn valid_result(n: int, heights: Seq<int>, result: int) -> bool {
    valid_input(n, heights) ==>
    (result == max_in_seq(heights) &&
    (forall|i: int| 0 <= i < heights.len() ==> heights[i] <= result) &&
    (exists|i: int| 0 <= i < heights.len() && heights[i] == result))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, heights: Seq<int>) -> (result: int)
    requires valid_input(n, heights)
    ensures valid_result(n, heights, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}