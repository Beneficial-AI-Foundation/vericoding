// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversions and indexing in helper functions */
proof fn max_subarray_helper(numbers: Seq<i32>, start: int, end: int) -> (sum: i32)
    requires
        0 <= start <= end <= numbers.len(),
    ensures
        sum == sum_range(numbers, start, end),
{
    if start == end {
        0
    } else {
        let sub_sum = max_subarray_helper(numbers, start, end - 1);
        sub_sum + numbers[index_as_int(end - 1)]
    }
}

spec fn sum_range(numbers: Seq<i32>, start: int, end: int) -> int
    requires
        0 <= start <= end <= numbers.len(),
{
    if start == end {
        0
    } else {
        numbers[index_as_int(end - 1)] as int + sum_range(numbers, start, end - 1)
    }
}

spec fn index_as_int(idx: int) -> int {
    idx
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
/* code modified by LLM (iteration 5): Fixed indexing and type conversion issues */
{
    let mut max_sum: i32 = 0;
    let mut start: usize = 0;
    
    while start < numbers.len()
        invariant
            max_sum >= 0,
            forall|s: usize, e: usize| s <= e && e <= numbers.len() && e <= start ==> {
                let mut sub_sum: i32 = 0;
                for i in s..e {
                    sub_sum = sub_sum + numbers[i];
                }
                sub_sum <= max_sum
            },
        decreases numbers.len() - start,
    {
        let mut current_sum: i32 = 0;
        let mut end: usize = start;
        
        while end < numbers.len()
            invariant
                current_sum >= 0,
                forall|e: usize| end <= e && e <= numbers.len() ==> {
                    let mut sub_sum: i32 = 0;
                    for i in start..e {
                        sub_sum = sub_sum + numbers[i];
                    }
                    sub_sum <= max_sum.max(current_sum)
                },
            decreases numbers.len() - end,
        {
            current_sum = current_sum + numbers[end];
            if current_sum > max_sum {
                max_sum = current_sum;
            }
            end = end + 1;
        }
        
        start = start + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}