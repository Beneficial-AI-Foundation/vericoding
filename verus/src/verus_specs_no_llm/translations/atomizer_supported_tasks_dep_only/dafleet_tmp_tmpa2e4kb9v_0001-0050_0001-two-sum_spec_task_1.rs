// Translated from Dafny
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
  && nums.index(i) + nums.index(j) == target
}

spec fn spec_twoSum(nums: Seq<int>, target: int) -> pair: (int, int)
    requires
        exists |i: int, j: int| correct_pair((i, j), nums, target)
    ensures
        correct_pair(pair, nums, target)
;

proof fn lemma_twoSum(nums: Seq<int>, target: int) -> (pair: (int, int))
    requires
        exists |i: int, j: int| correct_pair((i, j), nums, target)
    ensures
        correct_pair(pair, nums, target)
{
    (0, 0)
}

}