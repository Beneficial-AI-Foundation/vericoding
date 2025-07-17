// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_KthElement(arr: Vec<int>, k: int) -> result: int
    requires
        1 <= k <= arr.len()
    ensures
        result == arr.index(k - 1)
;

proof fn lemma_KthElement(arr: Vec<int>, k: int) -> (result: int)
    requires
        1 <= k <= arr.len()
    ensures
        result == arr.index(k - 1)
{
    0
}

}