// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_twoSum(nums: Vec<int>, target: int) -> index1: int, index2: int
    requires
        2 <= nums.len(),
        exists |i: int, j: int| (0 <= i < j < nums.len() && nums.index(i) + nums.index(j) == target)
    ensures
        index1 != index2,
        0 <= index1 < nums.len(),
        0 <= index2 < nums.len(),
        nums.index(index1) + nums.index(index2) == target
;

proof fn lemma_twoSum(nums: Vec<int>, target: int) -> (index1: int, index2: int)
    requires
        2 <= nums.len(),
        exists |i: int, j: int| (0 <= i < j < nums.len() && nums.index(i) + nums.index(j) == target)
    ensures
        index1 != index2,
        0 <= index1 < nums.len(),
        0 <= index2 < nums.len(),
        nums.index(index1) + nums.index(index2) == target
{
    (0, 0)
}

}