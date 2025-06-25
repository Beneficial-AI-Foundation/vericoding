use vstd::prelude::*;

verus! {

spec fn correct_pair(pair: (int, int), nums: Seq<int>, target: int) -> bool {
    let (i, j) = pair;
    && 0 <= i < nums.len()
    && 0 <= j < nums.len()
    && i != j
    && nums[i] + nums[j] == target
}

pub fn twoSum(nums: Seq<int>, target: int) -> (pair: (int, int))
    requires(exists|i: int, j: int| correct_pair((i, j), nums, target))
    ensures(correct_pair(pair, nums, target))
{
}

}