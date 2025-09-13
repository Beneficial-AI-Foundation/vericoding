// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn max_height_up_to(heights: Seq<int>, index: int) -> int
    recommends heights.len() > 0 && -1 <= index < heights.len()
    decreases index
{
    if index < 0 {
        0
    } else if index == 0 {
        heights[0]
    } else if heights[index] > max_height_up_to(heights, index - 1) {
        heights[index]
    } else {
        max_height_up_to(heights, index - 1)
    }
}

spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n >= 1 && heights.len() == n && (forall|i: int| 0 <= i < heights.len() ==> heights[i] >= 1)
}

spec fn can_make_non_decreasing(heights: Seq<int>) -> bool
    recommends heights.len() > 0
{
    forall|i: int| 0 <= i < heights.len() ==> heights[i] >= max_height_up_to(heights, i) - 1
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, heights: Seq<int>) -> (result: Seq<char>)
    requires valid_input(n, heights)
    ensures result =~= seq!['Y' as char, 'e' as char, 's' as char] <==> can_make_non_decreasing(heights)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    seq![]
    // impl-end
}
// </vc-code>


}

fn main() {}