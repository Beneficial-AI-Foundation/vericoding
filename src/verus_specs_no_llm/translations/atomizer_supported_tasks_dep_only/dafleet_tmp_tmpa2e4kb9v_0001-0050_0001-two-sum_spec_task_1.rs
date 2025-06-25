// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn correct_pair(pair: (int, int), nums: Seq<int>, target: int) -> bool {
    var (i, j) := pair;
  and 0 <= i < nums.len()
  and 0 <= j < nums.len()
  and i != j  // "you may not use the same element twice"
  and nums[i] + nums[j] == target
}

fn twoSum(nums: Seq<int>, target: int) -> pair: (int, int)
    requires exists|i: int, j: int| correct_pair((i, j), nums, target)
    ensures correct_pair(pair, nums, target)
{
}

}