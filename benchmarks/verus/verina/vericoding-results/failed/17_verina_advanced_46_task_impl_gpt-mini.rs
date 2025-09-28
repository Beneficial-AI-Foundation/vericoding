// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec function computing the sum of a slice numbers[start..end) used for reasoning */
spec fn slice_sum(numbers: &Vec<i32>, start: usize, end: usize) -> i32
    requires start <= end && end <= numbers.len(),
    decreases end - start
{
    if start == end {
        0
    } else {
        numbers[start] + slice_sum(numbers, start + 1, end)
    }
}

/* helper modified by LLM (iteration 5): small no-op proof helper retained for symmetry with earlier iterations */
proof fn helper_noop() {
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
    /* code modified by LLM (iteration 5): Kadane's algorithm computing the maximum subarray sum (non-negative variant) */
    let mut best: i32 = 0;
    let mut cur: i32 = 0;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            best >= 0,
            cur >= 0,
            i <= numbers.len(),
        decreases numbers.len() - i
    {
        let sum = cur + numbers[i];
        if sum < 0 {
            cur = 0;
        } else {
            cur = sum;
        }
        if cur > best {
            best = cur;
        }
        i = i + 1;
    }
    proof {
        assert(best >= 0);
    }
    best
}

// </vc-code>

}
fn main() {}