// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix exists syntax and use spec indexing */
spec fn first(nums: &Vec<i32>) -> i32 requires nums.len() > 0 { nums@[0] }

proof fn exists_index_ge_first(nums: &Vec<i32>, val: i32)
    requires nums.len() > 0 && val == first(nums)
    ensures exists|i: int| 0 <= i && i < nums.len() && val >= nums@[i]
{
    proof {
        assert(val == nums@[0]);
        assert(val >= nums@[0]);
        exists|i: int| 0 <= i && i < nums.len() && val >= nums@[i];
    }
}
// </vc-helpers>

// <vc-spec>
fn max_strength(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures

        exists|i: int| 0 <= i < nums.len() && result >= nums[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate to compute max and prove existence using correct exists syntax */
    let mut i: int = 1;
    let mut result: i32 = nums[0usize];
    while i < nums.len()
        invariant 0 <= i && i <= nums.len() && result >= nums@[0],
        decreases nums.len() - i
    {
        let v: i32 = nums[i as usize];
        if v > result {
            result = v;
        }
        i += 1;
    }
    proof {
        assert(result >= nums@[0]);
        exists|j: int| 0 <= j && j < nums.len() && result >= nums@[j];
    }
    result
}
// </vc-code>

}
fn main() {}