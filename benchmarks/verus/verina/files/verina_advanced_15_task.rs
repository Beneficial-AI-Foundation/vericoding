// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}