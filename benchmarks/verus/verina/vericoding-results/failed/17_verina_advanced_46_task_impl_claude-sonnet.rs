// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type consistency by using usize for indexing and i32 for values */
spec fn subarray_sum(numbers: &Vec<i32>, start: usize, end: usize) -> i32
    requires start <= end && end <= numbers.len()
{
    if start == end {
        0
    } else {
        numbers[start as int] + subarray_sum(numbers, start + 1, end)
    }
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
    /* code modified by LLM (iteration 5): Kadane's algorithm with proper type handling */
    let mut max_sum = 0i32;
    let mut current_sum = 0i32;
    
    for i in 0..numbers.len()
        invariant
            max_sum >= 0,
            current_sum >= 0,
    {
        current_sum = current_sum + numbers[i];
        if current_sum < 0 {
            current_sum = 0;
        }
        if current_sum > max_sum {
            max_sum = current_sum;
        }
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}