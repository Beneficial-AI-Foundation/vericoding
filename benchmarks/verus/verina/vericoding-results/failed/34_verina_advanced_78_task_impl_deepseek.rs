// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed return type syntax and ghost function signature */
proof fn find_indices_exists(nums: Seq<int>, target: int) -> (i: int, j: int)
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        0 <= i < j < nums.len(),
        nums[i] + nums[j] == target,
{
    choose|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target
}

proof fn convert_to_usize(i: int, j: int, nums_len: int) -> (usize, usize)
    requires
        0 <= i < nums_len,
        0 <= j < nums_len,
        i < j,
    ensures
        result.0 < result.1,
        result.0 < nums_len as usize,
        result.1 < nums_len as usize,
        result.0 as int == i,
        result.1 as int == j,
{
    (i as usize, j as usize)
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
{
    /* code modified by LLM (iteration 5): Executable function body with proper return */
    proof {
        let nums_spec = nums.view();
        let (i, j) = find_indices_exists(nums_spec, target as int);
        let result = convert_to_usize(i, j, nums_spec.len());
        result
    }
}
// </vc-code>

}
fn main() {}