// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, scores: Seq<int>) -> bool {
    n >= 1 && m >= 1 && scores.len() == n &&
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] >= 0 && #[trigger] scores[i] <= m
}

spec fn sum(nums: Seq<int>) -> int
    decreases nums.len()
{
    if nums.len() == 0 { 
        0 
    } else { 
        nums[0] + sum(nums.subrange(1, nums.len() as int)) 
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn valid_redistribution(original: Seq<int>, redistributed: Seq<int>, m: int) -> bool {
    redistributed.len() == original.len() &&
    sum(redistributed) == sum(original) &&
    forall|i: int| 0 <= i < redistributed.len() ==> #[trigger] redistributed[i] >= 0 && #[trigger] redistributed[i] <= m
}

spec fn max_possible_first_score(n: int, m: int, scores: Seq<int>) -> int {
    min(sum(scores), m)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, scores: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, scores@.map(|_i: int, x: i8| x as int)),
    ensures 
        result as int == max_possible_first_score(n as int, m as int, scores@.map(|_i: int, x: i8| x as int)),
        result as int == min(sum(scores@.map(|_i: int, x: i8| x as int)), m as int),
        exists|redistributed: Seq<int>| (valid_redistribution(scores@.map(|_i: int, x: i8| x as int), redistributed, m as int) && 
            redistributed[0] == result as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}