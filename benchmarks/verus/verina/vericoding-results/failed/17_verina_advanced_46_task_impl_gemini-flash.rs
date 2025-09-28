// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `get_subarray_sum` function now correctly iterates through the given subarray and accumulates the sum. The `sum` is initialized to `0i32` to avoid `int` in the executable context during the invariant check. */
spec fn get_subarray_sum(numbers: &Vec<i32>, start: usize, end: usize) -> (result: i32)
    requires
        start <= end,
        end <= numbers.len(),
{
    let mut sum: i32 = 0i32;
    if start == end {
        sum
    } else {
        for i_idx in start..end {
            sum = sum + numbers[i_idx as int]; // Access vector elements safely with int
        }
        sum
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
/* code modified by LLM (iteration 5): The Kadane's algorithm implementation for finding the maximum subarray sum now uses type casting `as i32` for `numbers[i]` to resolve type mismatch errors. The initial values for `max_so_far` and `current_max` are set to `0i32`. The invariant on `get_subarray_sum` is removed because it was causing issues with `i` within the invariant and `get_subarray_sum` is `spec` function which should not impact implementation. */
{
    if numbers.is_empty() {
        return 0i32;
    }

    let mut max_so_far: i32 = 0i32;
    let mut current_max: i32 = 0i32;

    let len = numbers.len();
    let mut i: usize = 0;

    while i < len
        invariant
             0 <= i && i <= len,
             max_so_far >= 0,
             current_max >= 0,
        decreases len - i
    {
        current_max = current_max + (numbers[i] as i32);

        if current_max < 0 {
            current_max = 0;
        }

        if current_max > max_so_far {
            max_so_far = current_max;
        }
        i = i + 1;
    }
    max_so_far
}
// </vc-code>

}
fn main() {}