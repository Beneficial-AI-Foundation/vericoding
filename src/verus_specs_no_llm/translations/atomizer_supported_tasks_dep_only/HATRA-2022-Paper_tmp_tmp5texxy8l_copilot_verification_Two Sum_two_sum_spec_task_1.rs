// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn twoSum(nums: Vec<int>, target: int) -> index1: int, index2: int
    requires 2 <= nums.len(),
             exists|i: int, j: int| (0 <= i < j < nums.len() and nums[i] + nums[j] == target)
    ensures index1 != index2,
            0 <= index1 < nums.len(),
            0 <= index2 < nums.len(),
            nums[index1] + nums[index2] == target
{
}

}