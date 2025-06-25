// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn removeElement(nums: Vec<int>, val: int) -> (i: int)
    ensures
        forall k :: 0 < k < i < nums.len() ==> nums.spec_index(k) != val
    modifies nums
{
    return 0;
}

}