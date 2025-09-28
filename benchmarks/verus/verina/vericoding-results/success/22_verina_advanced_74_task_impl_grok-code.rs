// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_min(nums: &Vec<u32>) -> (result: u32)
    requires nums.len() >=1,
    ensures
        forall |i: int| 0 <= i < nums.len() ==> nums[i] >= result,
        exists |i: int| 0 <= i < nums.len() && nums[i] == result
{
    /* helper modified by LLM (iteration 2): added invariant to ensure min is equal to some array element */
    let mut min = nums[0];
    let mut i = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            forall |j: int| 0 <= j < i ==> nums[j] >= min,
            exists |j: int| 0 <= j < i && nums[j] == min
        decreases nums.len() - i
    {
        if nums[i] < min {
            min = nums[i];
        }
        i += 1;
    }
    min
}
// </vc-helpers>

// <vc-spec>
fn solution(nums: Vec<u32>) -> (result: u32)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 1 && #[trigger] nums[i] <= 100,
    ensures
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): calls helper function to find minimum */
    let result = find_min(&nums);
    result
}
// </vc-code>

}
fn main() {}