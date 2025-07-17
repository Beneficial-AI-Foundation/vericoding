// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_removeElement(nums: Vec<int>, val: int) -> i: int
    ensures
        forall |k: int| 0 < k < i < nums.len() ==> nums.index(k) != val
    modifies nums
;

proof fn lemma_removeElement(nums: Vec<int>, val: int) -> (i: int)
    ensures
        forall |k: int| 0 < k < i < nums.len() ==> nums.index(k) != val
    modifies nums
{
    0
}

}