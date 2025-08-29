use vstd::prelude::*;


verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn smallest_num(nums: &Vec<i32>) -> (min: i32)
    // pre-conditions-start
    requires
        nums.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut min = nums[0];
    let mut i = 1;
    
    /* code modified by LLM (iteration 2): added decreases clause */
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            forall|j: int| 0 <= j < i ==> min <= nums[j],
            exists|j: int| 0 <= j < i && min == nums[j],
        decreases nums.len() - i
    {
        if nums[i] < min {
            min = nums[i];
        }
        i += 1;
    }
    
    min
}
// </vc-code>

} // verus!

fn main() {}