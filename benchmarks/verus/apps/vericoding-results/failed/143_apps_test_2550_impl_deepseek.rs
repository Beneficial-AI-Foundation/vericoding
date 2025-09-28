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
/* helper modified by LLM (iteration 5): removed invalid lemma and simplified helpers */
proof fn lemma_min_sum_upper_bound(sum_val: int, m_val: int) by(nonlinear_arith)
    ensures
        min(sum_val, m_val) <= m_val,
        min(sum_val, m_val) <= sum_val,
        min(sum_val, m_val) == if sum_val <= m_val { sum_val } else { m_val }
{
}

proof fn lemma_cast_i8_bound(x: i8, m: i8)
    requires
        x >= 0,
        x <= m
    ensures
        x as int >= 0,
        x as int <= m as int
{
}
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
    /* code modified by LLM (iteration 5): simplified implementation with direct min calculation */
    let total: i32 = scores.iter().fold(0, |acc, &x| acc + x as i32);
    let min_val = if total <= m as i32 { total as i8 } else { m };
    min_val
}
// </vc-code>


}

fn main() {}