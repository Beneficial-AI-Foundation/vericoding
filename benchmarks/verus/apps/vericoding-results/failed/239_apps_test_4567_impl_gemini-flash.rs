// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(scores: Seq<int>) -> bool {
    scores.len() > 0 && scores.len() <= 100 &&
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] >= 1 && #[trigger] scores[i] <= 100
}

spec fn sum_seq(scores: Seq<int>) -> int
    decreases scores.len()
{
    if scores.len() == 0 {
        0
    } else {
        scores[0] + sum_seq(scores.subrange(1, scores.len() as int))
    }
}

spec fn all_multiples_of_10(scores: Seq<int>) -> bool {
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] % 10 == 0
}

spec fn is_smallest_non_multiple(scores: Seq<int>, value: int) -> bool {
    scores.contains(value) && 
    value % 10 != 0 &&
    forall|x: int| #[trigger] scores.contains(x) && x % 10 != 0 ==> value <= x
}

spec fn correct_result(scores: Seq<int>, result: int) -> bool {
    let total_sum = sum_seq(scores);
    if total_sum % 10 != 0 {
        result == total_sum
    } else if all_multiples_of_10(scores) {
        result == 0
    } else {
        exists|smallest_non_multiple: int| 
            is_smallest_non_multiple(scores, smallest_non_multiple) &&
            result == total_sum - smallest_non_multiple
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add an empty placeholder to fix errors related to empty helper sections. */

// </vc-helpers>

// <vc-spec>
fn solve(scores: Vec<i8>) -> (result: i8)
    requires valid_input(scores@.map(|i, x| x as int))
    ensures correct_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix compilation errors by correctly using ghost blocks for ghost code and casting to i8 at the end. */
{
    let scores_seq: Seq<int>;
    proof {
        scores_seq = scores@.map(|i, x| x as int);
    }
    let total_sum = sum_seq(scores_seq);

    if total_sum % 10 != 0 {
        return total_sum as i8;
    }

    let mut smallest_non_multiple_found: int;
    proof {
        smallest_non_multiple_found = 200; // Larger than any possible score
    }
    let mut found_non_multiple: bool = false;

    // Find the smallest score that is not a multiple of 10
    for i in 0..scores.len() {
        let score: int;
        proof {
            score = scores@[i] as int;
        }
        if score % 10 != 0 {
            if !found_non_multiple || score < smallest_non_multiple_found {
                smallest_non_multiple_found = score;
                found_non_multiple = true;
            }
        }
    }

    if !found_non_multiple {
        // All scores are multiples of 10
        return 0i8;
    } else {
        return (total_sum - smallest_non_multiple_found) as i8;
    }
}
// </vc-code>


}

fn main() {}