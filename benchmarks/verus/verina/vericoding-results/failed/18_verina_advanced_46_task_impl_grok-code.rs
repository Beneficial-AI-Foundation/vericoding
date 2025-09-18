// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No modifications needed */
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
    /* code modified by LLM (iteration 5): Fixed compilation errors by using usize for indexing and vector access instead of nat and sequence access */
    let mut current_sum: i32 = 0;
    let mut max_sum: i32 = 0;
    let mut index: usize = 0;
    let len: usize = numbers.len();
    while index < len {
        let num = numbers[index];
        current_sum = if current_sum + num < 0 { 0 } else { current_sum + num };
        if current_sum > max_sum {
            max_sum = current_sum;
        }
        index += 1;
    }
    max_sum
}
// </vc-code>

}
fn main() {}