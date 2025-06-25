// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn twoSum(nums: Vec<int>, target: int) -> i: int, j: int
    requires nums.len() > 1,
             exists|i: int, j: int|0 <= i < j < nums.len() and  nums[i] + nums[j] == target
    ensures 0 <= i < j < nums.len() and nums[i] + nums[j] == target,
            forall|ii: int, jj: int| (0 <= ii < i and ii < jj < nums.len())  ==> nums[ii] + nums[jj] != target,
            forall|jj: int| i < jj < j ==> nums[i] + nums[jj] != target
{
}

}