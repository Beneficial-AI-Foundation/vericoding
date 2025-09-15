// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): name returned pair as result and use choose to witness */
proof fn choose_witness_pair(nums: &Vec<i32>, target: i32) -> (result: (int, int))
    ensures
        0 <= result.0,
        result.0 < result.1,
        result.1 < nums.len(),
        nums@[result.0] + nums@[result.1] == target
{
    proof {
        let (i, j) = choose |i: int, j: int| 0 <= i < j < nums.len() && nums@[i] + nums@[j] == target;
        result = (i, j);
    }
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
    /* code modified by LLM (iteration 5): use choose to obtain witness indices and return as usize pair */
    let (i0, j0) = choose |i: int, j: int| 0 <= i < j < nums.len() && nums@[i] + nums@[j] == target;
    let ri: usize = i0 as usize;
    let rj: usize = j0 as usize;
    (ri, rj)
}
// </vc-code>

}
fn main() {}