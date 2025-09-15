// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause to recursive spec functions */
spec fn sum_subarray(numbers: &Vec<i32>, start: usize, end: usize) -> int
    recommends start <= end <= numbers.len()
    decreases end - start
{
    if start == end {
        0
    } else {
        numbers[start as int] as int + sum_subarray(numbers, (start + 1) as usize, end)
    }
}

spec fn max_sum_ending_at(numbers: &Vec<i32>, i: usize) -> int
    recommends i <= numbers.len()
    decreases i
{
    if i == 0 {
        0
    } else {
        let prev = max_sum_ending_at(numbers, (i - 1) as usize);
        let with_current = prev + numbers[(i - 1) as int] as int;
        if with_current > numbers[(i - 1) as int] as int {
            if with_current > 0 {
                with_current
            } else {
                0
            }
        } else {
            if numbers[(i - 1) as int] as int > 0 {
                numbers[(i - 1) as int] as int
            } else {
                0
            }
        }
    }
}

spec fn max_sum_up_to(numbers: &Vec<i32>, i: usize) -> int
    recommends i <= numbers.len()
    decreases i
{
    if i == 0 {
        0
    } else {
        let prev_max = max_sum_up_to(numbers, (i - 1) as usize);
        let current_max = max_sum_ending_at(numbers, i);
        if current_max > prev_max {
            current_max
        } else {
            prev_max
        }
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
/* code modified by LLM (iteration 5): Added decreases clause to while loop */
{
    let mut max_sum: i32 = 0;
    let mut current_sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            max_sum >= 0,
            current_sum >= 0,
            max_sum == max_sum_up_to(numbers, i) as i32,
            current_sum == max_sum_ending_at(numbers, i) as i32,
        decreases numbers.len() - i
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