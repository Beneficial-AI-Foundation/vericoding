// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int, heights: Seq<int>) -> bool {
    n >= 1 && k >= 1 && heights.len() == n && 
    forall|i: int| 0 <= i < heights.len() ==> heights[i] >= 1
}

spec fn count_eligible(heights: Seq<int>, k: int) -> int {
    heights.filter(|height: int| height >= k).len() as int
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, heights: Seq<int>) -> (count: int)
    requires 
        valid_input(n, k, heights)
    ensures 
        0 <= count <= heights.len(),
        count == count_eligible(heights, k)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}