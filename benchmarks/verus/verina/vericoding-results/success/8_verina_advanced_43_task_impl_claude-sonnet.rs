// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause to fix compilation error */
fn is_max_in_slice(nums: &Vec<i32>, max_val: i32) -> bool
{
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|j: int| 0 <= j < i ==> nums[j] <= max_val,
        decreases nums.len() - i
    {
        if nums[i] > max_val {
            return false;
        }
        i += 1;
    }
    true
}

fn contains_value(nums: &Vec<i32>, val: i32) -> bool
{
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|j: int| 0 <= j < i ==> nums[j] != val,
        decreases nums.len() - i
    {
        if nums[i] == val {
            return true;
        }
        i += 1;
    }
    false
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
    /* code modified by LLM (iteration 2): added decreases clause to fix compilation error */
    let mut max_val = nums[0];
    let mut i = 1;
    
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            exists|k: int| 0 <= k < nums.len() && max_val >= nums[k],
            forall|j: int| 0 <= j < i ==> nums[j] <= max_val,
        decreases nums.len() - i
    {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }
    
    max_val
}
// </vc-code>

}
fn main() {}