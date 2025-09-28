// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn two_sum(nums: &Vec<i32>, target: i32) -> (result: (usize, usize))
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        result.0 < result.1,
        result.0 < nums.len(),
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Adjusted invariants to use integer lengths for bounds checking to satisfy preconditions for vector indexing. */
    let n: usize = nums.len();
    let len: int = n as int;
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            0 <= i < len,
            forall|k: int, l: int| 0 <= k < i && k < l < len ==> nums@[k] + nums@[l] != target,
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                0 <= i < len,
                i <= j < len,
            decreases n - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}