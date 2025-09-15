// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type annotations to use i32 instead of usize for indices */
spec fn subarray_sum(numbers: &Vec<i32>, start: int, end: int) -> i32
    requires 0 <= start <= end && end <= numbers.len()
{
    if start == end {
        0
    } else {
        numbers[start as usize] + subarray_sum(numbers, start + 1, end)
    }
}

proof fn subarray_sum_nonnegative_empty(numbers: &Vec<i32>)
    ensures subarray_sum(numbers, 0, 0) == 0
{
}

proof fn max_nonnegative(a: i32, b: i32)
    ensures if a >= b { a } else { b } >= 0 ==> a >= 0 || b >= 0
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
    /* code modified by LLM (iteration 5): fixed invariant syntax by removing braces */
    let mut max_sum = 0;
    let mut current_sum = 0;
    let mut i = 0;
    
    while i < numbers.len()
        invariant 
            i <= numbers.len() &&
            max_sum >= 0 &&
            current_sum >= 0
    {
        current_sum += numbers[i];
        if current_sum < 0 {
            current_sum = 0;
        }
        if current_sum > max_sum {
            max_sum = current_sum;
        }
        i += 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}