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
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
        forall|i: int, j: int| 0 <= i < j < nums.len() && i < result.0 as int ==> nums[i] + nums[j] != target,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed indexing errors by removing unnecessary as int casts in executable code */
let mut i: usize = 0;
while i < nums.len()
    invariant
        0 <= i <= nums.len()
    decreases nums.len() - i
{
    let mut j: usize = i + 1;
    while j < nums.len()
        invariant
            i < j <= nums.len()
        decreases nums.len() - j
    {
        if nums[i] + nums[j] == target {
            return (i, j);
        }
        j += 1;
    }
    i += 1;
}
    // unreachable due to precondition
    (0, 1)
}
// </vc-code>

}
fn main() {}