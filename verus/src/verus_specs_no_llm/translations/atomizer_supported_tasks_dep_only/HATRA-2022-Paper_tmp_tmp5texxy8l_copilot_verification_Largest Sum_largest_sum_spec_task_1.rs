// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum_Array(arr: Vec<int>, start: int, stop: int) -> int
    requires
        0 <= start <= stop <= arr.len()
    reads arr
{
    0
}

spec fn spec_largest_sum(nums: Vec<int>, k: int) -> sum: int
    requires
        nums.len() > 0
    ensures
        max_sum_subarray(nums, sum, 0, nums.len())
;

proof fn lemma_largest_sum(nums: Vec<int>, k: int) -> (sum: int)
    requires
        nums.len() > 0
    ensures
        max_sum_subarray(nums, sum, 0, nums.len())
{
    0
}

}