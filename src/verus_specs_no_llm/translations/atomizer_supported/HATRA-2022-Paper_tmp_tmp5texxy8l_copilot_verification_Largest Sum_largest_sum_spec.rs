// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn largest_sum(nums: Vec<int>, k: int) -> (sum: int)
    requires nums.len() > 0
    ensures max_sum_subarray(nums, sum, 0, nums.len())
{
}

}