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
    let total: int = 0;
    let mut index = 0;
    while index < scores.len()
        invariant
            0 <= index <= scores.len(),
            total == sum_seq(scores@.map(|i, x| x as int).subrange(0, index)),
        decreases scores.len() - index
    {
        total += scores[index] as int;
        index += 1;
    }

    let mut all_multiples = true;
    let mut smallest_non_multiple = 0;
    index = 0;
    while index < scores.len()
        invariant
            0 <= index <= scores.len(),
            all_multiples ==> (forall|i: int| 0 <= i < index ==> scores@[i] % 10 == 0),
            !all_multiples ==> 
                smallest_non_multiple > 0 && 
                exists|i: int| 0 <= i < index && scores@[i] % 10 != 0 && scores@[i] as int == smallest_non_multiple &&
                forall|i: int| 0 <= i < index && scores@[i] % 10 != 0 ==> smallest_non_multiple <= scores@[i] as int,
        decreases scores.len() - index
    {
        let score = scores[index] as int;
        if score % 10 != 0 {
            if all_multiples {
                all_multiples = false;
                smallest_non_multiple = score;
            } else {
                if score < smallest_non_multiple {
                    smallest_non_multiple = score;
                }
            }
        }
        index += 1;
    }

    if total % 10 != 0 {
        total as i8
    } else if all_multiples {
        0
    } else {
        (total - smallest_non_multiple) as i8
    }
}
// </vc-code>


}

fn main() {}