// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn longest_increasing_subsequence(nums: Vec<int>) -> (max: int)
    requires 1 <= nums.len() <= 2500,
             forall|i: int| 0 <= i < nums.len() ==> -10000 <= nums[i] <= 10000
    // TODO: modify the
    ensures clause so that max is indeed equal to the longest increasing subsequence,
            max >= 1
{
}

}