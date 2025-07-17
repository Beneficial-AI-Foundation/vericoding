// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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