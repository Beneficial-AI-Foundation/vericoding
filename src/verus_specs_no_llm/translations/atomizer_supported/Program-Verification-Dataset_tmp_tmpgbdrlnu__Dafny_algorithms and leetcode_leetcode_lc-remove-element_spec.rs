// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn removeElement(nums: Vec<int>, val: int) -> (i: int)
    ensures forall|k: int| 0 < k < i < nums.len() ==> nums[k] != val
    modifies nums
{
}

}