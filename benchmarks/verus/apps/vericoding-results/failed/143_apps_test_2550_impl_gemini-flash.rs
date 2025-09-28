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
    /* code modified by LLM (iteration 5): Fixed compilation error by moving `scores_int`, `total_sum_spec`, and `m_spec` into ghost context when they are used in spec functions. */
    let result_val: i8;

    proof {
        let scores_int = scores@.map(|_i: int, x: i8| x as int);
        let total_sum_spec = sum(scores_int);
        let m_spec = m as int;

        if total_sum_spec <= m_spec {
            result_val = total_sum_spec as i8;
            let mut redistributed = Seq::<int>::new();
            redistributed = redistributed.push(total_sum_spec);
            for i in 1..n as int {
                redistributed = redistributed.push(0);
            }
            assert(redistributed.len() == n as int);
            assert(sum(redistributed) == total_sum_spec);
            assert(total_sum_spec <= m_spec);
            assert(forall|i: int| 0 <= i < redistributed.len() ==> redistributed[i] >= 0 && redistributed[i] <= m_spec);
            assert(redistributed[0] == total_sum_spec);
            assert(valid_redistribution(scores_int, redistributed, m_spec));
        } else {
            result_val = m as i8;
            let mut redistributed = Seq::<int>::new();
            redistributed = redistributed.push(m_spec);

            let remaining_sum = total_sum_spec - m_spec;
            let mut current_remaining_sum = remaining_sum;

            for i in 1..n as int
                invariant
                    i <= n as int,
                    redistributed.len() == i + 1,
                    sum(redistributed.subrange(0, i as int)) + current_remaining_sum == total_sum_spec,
                    forall|j: int| 0 <= j < redistributed.len() ==> redistributed[j] >= 0 && redistributed[j] <= m_spec,
            {
                if current_remaining_sum >= m_spec {
                    redistributed = redistributed.push(m_spec);
                    current_remaining_sum = current_remaining_sum - m_spec;
                } else if current_remaining_sum > 0 {
                    redistributed = redistributed.push(current_remaining_sum);
                    current_remaining_sum = 0;
                } else {
                    redistributed = redistributed.push(0);
                }
            }
            assert(redistributed.len() == n as int);
            assert(sum(redistributed) == total_sum_spec); 
            assert(redistributed[0] == m_spec);
            assert(forall|k: int| 0 <= k < redistributed.len() ==> redistributed[k] >= 0);
            assert(forall|k: int| 0 <= k < redistributed.len() ==> redistributed[k] <= m_spec);
            assert(valid_redistribution(scores_int, redistributed, m_spec));
        }
    }
    
    result_val
}
// </vc-code>


}

fn main() {}