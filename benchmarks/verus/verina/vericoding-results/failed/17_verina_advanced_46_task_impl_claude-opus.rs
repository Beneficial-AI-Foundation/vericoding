// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): Fixed type mismatches - use usize arithmetic and proper indexing */
    let mut max_sum: i32 = 0;
    let mut current_sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            current_sum >= 0,
            max_sum >= 0,
            max_sum >= current_sum,
            forall|start: usize, end: usize| start < i && start <= end && end <= i ==> {
                let mut subarray_sum: i32 = 0;
                let mut j: usize = start;
                while j < end
                    invariant
                        start <= j <= end,
                        end <= i
                {
                    subarray_sum = subarray_sum + numbers[j];
                    j = j + 1usize;
                }
                subarray_sum <= max_sum
            }
    {
        current_sum = current_sum + numbers[i];
        if current_sum < 0 {
            current_sum = 0;
        }
        if current_sum > max_sum {
            max_sum = current_sum;
        }
        i = i + 1usize;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}