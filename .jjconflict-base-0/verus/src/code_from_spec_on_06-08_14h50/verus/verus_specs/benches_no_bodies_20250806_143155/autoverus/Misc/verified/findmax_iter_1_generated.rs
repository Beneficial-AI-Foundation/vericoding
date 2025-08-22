#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
fn find_max(nums: Vec<i32>) -> (ret:i32)
requires
    nums.len() > 0,
ensures
    forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
    exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
{
    let mut max = nums[0];
    let mut idx = 0;
    
    while idx < nums.len()
        invariant
            0 <= idx <= nums.len(),
            forall |i: int| 0 <= i < idx ==> nums@[i] <= max,
            exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == max,
    {
        if nums[idx] > max {
            max = nums[idx];
        }
        idx = idx + 1;
    }
    
    max
}
}