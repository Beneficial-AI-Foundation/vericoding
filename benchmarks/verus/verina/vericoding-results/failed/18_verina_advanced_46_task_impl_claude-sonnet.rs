// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed requires/ensures from spec function and added helper lemma */
spec fn sum_subarray(numbers: &Vec<i32>, start: usize, end: usize) -> int
{
    if start >= end || end > numbers.len() {
        0
    } else {
        numbers[start as int] + sum_subarray(numbers, (start + 1) as usize, end)
    }
}

proof fn sum_subarray_bounds(numbers: &Vec<i32>, start: usize, end: usize)
    requires
        start <= end,
        end <= numbers.len(),
    ensures
        sum_subarray(numbers, start, end) >= 0 ==> 
            forall|max_val: i32| max_val >= 0 ==> sum_subarray(numbers, start, end) <= max_val || max_val >= sum_subarray(numbers, start, end),
    decreases end - start
{
}
// </vc-helpers>

// <vc-spec>
fn max_subarray_sum(numbers: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        forall|start: usize, end: usize| {
            start <= end && end <= numbers.len()
        } ==> {
            let mut subarray_sum: i32 = 0;
            subarray_sum <= result
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented Kadane's algorithm with stronger invariants */
    let mut max_sum: i32 = 0;
    let mut current_sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            max_sum >= 0,
            current_sum >= 0,
            forall|start: usize, end: usize| {
                start <= end && end <= i
            } ==> {
                sum_subarray(numbers, start, end) <= max_sum
            },
    {
        current_sum = current_sum + numbers[i];
        if current_sum < 0 {
            current_sum = 0;
        }
        if current_sum > max_sum {
            max_sum = current_sum;
        }
        i = i + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}