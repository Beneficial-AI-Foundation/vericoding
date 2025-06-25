// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn correct_pair(pair: (int, int), nums: Seq<int>, target: int) -> bool {
    var (i, j) := pair;
  && 0 <= i < nums.len()
  && 0 <= j < nums.len()
  && i != j  // "you may not use the same element twice"
  && nums.spec_index(i) + nums.spec_index(j) == target
}

fn twoSum(nums: Seq<int>, target: int) -> (pair: (int, int))
    requires
        exists i, j :: correct_pair((i, j), nums, target)
    ensures
        correct_pair(pair, nums, target)
{
    return (0, 0);
}

}