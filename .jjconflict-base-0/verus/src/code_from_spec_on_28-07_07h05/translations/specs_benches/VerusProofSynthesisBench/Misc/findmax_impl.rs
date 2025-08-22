#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
fn find_max(nums: Vec<i32>) -> (ret:i32)
    // pre-conditions-start
    requires
        nums.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
        exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
    // post-conditions-end
{
    let mut max_val = nums[0];
    let mut idx = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < nums.len()
        invariant
            0 < idx <= nums.len(),
            forall |i: int| 0 <= i < idx ==> nums@[i] <= max_val,
            exists |i: int| 0 <= i < idx && nums@[i] == max_val,
        decreases nums.len() - idx
    {
        if nums[idx] > max_val {
            max_val = nums[idx];
        }
        idx += 1;
    }
    
    max_val
}
}

fn main() {}