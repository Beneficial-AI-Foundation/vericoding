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
/* helper modified by LLM (iteration 5): removed block syntax and let bindings from invariants to fix compilation error */
fn compute_sum(v: &Vec<i8>) -> (result: i32)
    ensures
        result == sum_seq(v@.map(|i, x: i8| x as int))
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum == sum_seq(v@.subrange(0, i as int).map(|i, x: i8| x as int))
        decreases v.len() - i
    {
        sum = #[verifier::truncate] sum + (v[i] as i32);
        i = i + 1;
    }
    sum
}

fn smallest_non_multiple(v: &Vec<i8>) -> (result: Option<i8>)
    ensures
        result is Some ==> is_smallest_non_multiple(v@.map(|i, x: i8| x as int), result->0 as int),
        result is None ==> all_multiples_of_10(v@.map(|i, x: i8| x as int))
{
    let mut min_val: Option<i8> = None;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            min_val is Some ==> min_val->0 as int % 10 != 0,
            min_val is Some ==> forall|k: int| 0 <= k < i ==> #[trigger] v@.contains(min_val->0 as int),
            min_val is Some ==> forall|k: int| 0 <= k < i ==> #[trigger] (v@[k] as int % 10 != 0) ==> min_val->0 as int <= v@[k] as int,
            min_val is None ==> forall|k: int| 0 <= k < i ==> #[trigger] (v@[k] as int % 10 == 0)
        decreases v.len() - i
    {
        if (v[i] as i32 % 10) != 0 {
            match min_val {
                Some(current_min) => if v[i] < current_min { min_val = Some(v[i]); },
                None => min_val = Some(v[i])
            }
        }
        i = i + 1;
    }
    min_val
}
// </vc-helpers>

// <vc-spec>
fn solve(scores: Vec<i8>) -> (result: i8)
    requires valid_input(scores@.map(|i, x| x as int))
    ensures correct_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed as compilation error was in helpers */
{
    let total_sum = compute_sum(&scores);
    if total_sum % 10 != 0 {
        #[verifier::truncate] total_sum as i8
    } else {
        let smallest = smallest_non_multiple(&scores);
        match smallest {
            Some(s) => #[verifier::truncate] (total_sum - (s as i32)) as i8,
            None => 0
        }
    }
}
// </vc-code>


}

fn main() {}