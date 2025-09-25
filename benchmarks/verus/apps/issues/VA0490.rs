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
fn solve(n: i8, k: i8, heights: Vec<i8>) -> (count: i8)
    requires 
        valid_input(n as int, k as int, heights@.ext_equal(heights@.map_values(|x| x as int)))
    ensures 
        0 <= count as int <= heights@.len(),
        count as int == count_eligible(heights@.map_values(|x| x as int), k as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}