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

// </vc-helpers>

// <vc-spec>
fn solve(scores: Vec<i8>) -> (result: i8)
    requires valid_input(scores@.map(|i, x| x as int))
    ensures correct_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    let mut total_sum: i32 = 0;
    let mut smallest_non_multiple: i32 = 101;
    let mut i: usize = 0;
    let scores_int = scores@.map(|_i, x| x as int);

    while i < scores.len()
        invariant
            0 <= i <= scores.len(),
            total_sum as int == sum_seq(scores_int.subrange(0, i as int)),
            (smallest_non_multiple == 101) == all_multiples_of_10(scores_int.subrange(0, i as int)),
            smallest_non_multiple != 101 ==> is_smallest_non_multiple(scores_int.subrange(0, i as int), smallest_non_multiple as int),
        decreases scores.len() - i
    {
        let current_score = scores[i] as i32;
        total_sum = total_sum + current_score;
        
        if current_score % 10 != 0 {
            if current_score < smallest_non_multiple {
                smallest_non_multiple = current_score;
            }
        }

        i = i + 1;
    }

    if total_sum % 10 != 0 {
        return total_sum as i8;
    } else {
        if smallest_non_multiple == 101 {
            return 0i8;
        } else {
            return (total_sum - smallest_non_multiple) as i8;
        }
    }
}
// </vc-code>


}

fn main() {}