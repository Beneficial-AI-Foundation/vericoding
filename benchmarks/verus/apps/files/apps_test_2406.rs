// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n &&
    (forall|i: int| 0 <= i < n ==> heights[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> heights[i] < heights[i+1])
}

spec fn valid_output(n: int, result: Seq<int>) -> bool {
    result.len() == n &&
    (forall|i: int| 0 <= i < n ==> result[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> result[i] <= result[i+1]) &&
    (forall|i: int| 0 <= i < n-1 ==> result[i+1] - result[i] <= 1)
}

spec fn is_stable(result: Seq<int>) -> bool {
    forall|i: int| 0 <= i < result.len()-1 ==> !(result[i] + 2 <= result[i+1])
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, heights: Seq<int>) -> (result: Seq<int>)
    requires 
        valid_input(n, heights)
    ensures 
        valid_output(n, result),
        sum_seq(result) == sum_seq(heights),
        is_stable(result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}