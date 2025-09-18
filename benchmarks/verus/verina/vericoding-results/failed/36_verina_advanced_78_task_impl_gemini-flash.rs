// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type mismatch for `nums` indexing, converting `idx` and `jdx` from `int` to `usize` before using them as array indices. */
fn find_two_sum_indices(nums: &Vec<i32>, target: i32) -> (result: (usize, usize))
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        result.0 < result.1,
        result.0 < nums.len(),
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
{
    let n = nums.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            n == nums.len(),
            forall|idx: int| 0 <= idx < i as int ==> 
                forall|jdx: int| idx < jdx < n as int ==> 
                    nums[idx as usize] + nums[jdx as usize] != target,
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                0 <= i as int,
                i < j,
                j <= n,
                n == nums.len(),
                forall|kdx: int| (i as int) < kdx && kdx < (j as int) ,
            decreases n - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    // This part should be unreachable given the precondition.
    // We add an assert(false) in a proof block to reflect this.
    proof {
        assert(false);
    }
    // Providing a dummy return value for the compiler, as the precondition guarantees 
    // that a valid pair will always be found.
    (0, 1) 
}
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
/* code modified by LLM (iteration 5): Call the fixed helper function `find_two_sum_indices`. */
{
    let (idx1, idx2) = find_two_sum_indices(&nums, target);
    (idx1, idx2)
}
// </vc-code>

}
fn main() {}