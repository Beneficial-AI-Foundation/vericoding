// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed indexing type issues in subarray_sum spec function */
spec fn subarray_sum(v: &Vec<i32>, start: int, end: int) -> i32
    requires
        0 <= start <= end <= (v.len() as int),
    decreases (end - start) as nat,
{
    if start == end { 0 as i32 } else { subarray_sum(v, start, end - 1) + v[end - 1] }
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
/* code modified by LLM (iteration 5): implemented Kadane's algorithm for maximum subarray sum */
{
    if numbers.is_empty() {
        0
    } else {
        let mut global_max: i32 = numbers[0];
        let mut current_max: i32 = numbers[0];
        let mut i = 1;
        while i < numbers.len()
            invariant
                1 <= i <= numbers.len(),
            decreases numbers.len() - i
        {
            current_max = core::cmp::max(current_max + numbers[i], numbers[i]);
            global_max = core::cmp::max(global_max, current_max);
            i += 1;
        }
        global_max
    }
}
// </vc-code>

}
fn main() {}