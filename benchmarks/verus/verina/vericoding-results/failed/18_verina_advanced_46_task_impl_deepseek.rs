// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn max_subarray_sum_helper(numbers: Seq<int>, start: usize, end: usize) -> (sum: int)
    requires
        start <= end <= numbers.len(),
    ensures
        sum == numbers.subrange(start as int, end as int).sum(),
    decreases end - start
{
    if start == end {
        0
    } else {
        let partial_sum = max_subarray_sum_helper(numbers, start, end - 1);
        partial_sum + numbers[end - 1]
    }
}

proof fn max_subarray_exists(numbers: Seq<int>) -> (max_sum: int)
    requires
        numbers.len() >= 0,
    ensures
        max_sum >= 0,
        forall|start: usize, end: usize|
            start <= end <= numbers.len()
            ==> numbers.subrange(start as int, end as int).sum() <= max_sum,
    decreases numbers.len()
{
    if numbers.len() == 0 {
        0
    } else {
        let prefix = numbers.subrange(0, numbers.len() as int - 1);
        let max_prefix = max_subarray_exists(prefix);
        let current_sum = numbers.subrange(0, numbers.len() as int).sum();
        if current_sum > max_prefix {
            current_sum
        } else {
            max_prefix
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
{
    let mut max_so_far = 0i32;
    let mut current_max = 0i32;
    let n = numbers.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            max_so_far >= 0,
            current_max >= 0,
            forall|start: usize, end: usize| {
                start <= end <= i
            } ==> {
                let mut subarray_sum: i32 = 0;
                subarray_sum <= max_so_far
            }
    {
        current_max = current_max + numbers[i];
        if current_max < 0 {
            current_max = 0;
        }
        if max_so_far < current_max {
            max_so_far = current_max;
        }
        i = i + 1;
    }
    
    max_so_far
}
// </vc-code>

}
fn main() {}