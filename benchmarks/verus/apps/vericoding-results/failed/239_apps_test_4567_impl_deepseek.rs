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
/* helper modified by LLM (iteration 5): fix pattern matching issue and improve verification */
fn find_smallest_non_multiple(scores: &Vec<i8>) -> (smallest: i8)
    requires
        scores@.len() > 0,
        exists|i: int| 0 <= i < scores@.len() && scores@[i] as int % 10 != 0
    ensures
        is_smallest_non_multiple(scores@.map(|i, x| x as int), smallest as int)
{
    let mut smallest = scores[0];
    let mut found_non_multiple = false;
    let mut i = 0;
    
    while i < scores.len()
        invariant
            0 <= i <= scores@.len(),
            (found_non_multiple ==> smallest as int % 10 != 0) || !found_non_multiple,
            forall|j: int| 0 <= j < i ==> smallest as int <= scores@[j] as int,
            exists|k: int| 0 <= k < i && scores@[k] as int % 10 != 0 ==> found_non_multiple
        decreases scores@.len() - i
    {
        let current = scores[i];
        if current % 10 != 0 {
            if !found_non_multiple || current < smallest {
                smallest = current;
                found_non_multiple = true;
            }
        }
        i += 1;
    }
    proof {
        assert forall|x: int| #[trigger] scores@.map(|i, x| x as int).contains(x) && x % 10 != 0 implies smallest as int <= x by {
            let j = choose|j: int| 0 <= j < scores@.len() && scores@[j] as int == x;
            assert(j < i);
        };
    }
    smallest
}
// </vc-helpers>

// <vc-spec>
fn solve(scores: Vec<i8>) -> (result: i8)
    requires valid_input(scores@.map(|i, x| x as int))
    ensures correct_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix iterator pattern matching issue and use manual summation */
{
    let mut total_sum: i32 = 0;
    let mut i = 0;
    while i < scores.len()
        invariant
            0 <= i <= scores@.len(),
            total_sum == sum_seq(scores@.subrange(0, i).map(|j, x| x as int))
        decreases scores@.len() - i
    {
        total_sum += scores[i] as i32;
        i += 1;
    }
    
    if total_sum % 10 != 0 {
        return total_sum as i8;
    }
    
    let mut all_multiple = true;
    let mut j = 0;
    while j < scores.len()
        invariant
            0 <= j <= scores@.len(),
            all_multiple == forall|k: int| 0 <= k < j ==> scores@[k] as int % 10 == 0
        decreases scores@.len() - j
    {
        if scores[j] % 10 != 0 {
            all_multiple = false;
        }
        j += 1;
    }
    
    if all_multiple {
        return 0;
    }
    
    let smallest_non_multiple = find_smallest_non_multiple(&scores);
    let result = total_sum - smallest_non_multiple as i32;
    result as i8
}
// </vc-code>


}

fn main() {}