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
spec fn to_int_seq(scores: Seq<i8>) -> Seq<int> {
    scores.map(|i, x| x as int)
}

spec fn is_multiple_of_10(x: int) -> bool {
    x % 10 == 0
}
// </vc-helpers>

// <vc-spec>
fn solve(scores: Vec<i8>) -> (result: i8)
    requires valid_input(scores@.map(|i, x| x as int))
    ensures correct_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    let n = scores.len();
    let mut sum: i32 = 0;
    let mut all_mult_10: bool = true;
    let mut min_non_mult_10: i32 = 1_000_000;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            0 <= i as int <= n as int,
        decreases n as int - i as int
    {
        let v_i32: i32 = scores[i] as i32;
        sum += v_i32;
        if v_i32 % 10 != 0 {
            all_mult_10 = false;
            if v_i32 < min_non_mult_10 {
                min_non_mult_10 = v_i32;
            }
        }
        i += 1;
    }
    if sum % 10 != 0 {
        return sum as i8;
    } else if all_mult_10 {
        return 0i8;
    } else {
        let r: i32 = sum - min_non_mult_10;
        return r as i8;
    }
}
// </vc-code>


}

fn main() {}