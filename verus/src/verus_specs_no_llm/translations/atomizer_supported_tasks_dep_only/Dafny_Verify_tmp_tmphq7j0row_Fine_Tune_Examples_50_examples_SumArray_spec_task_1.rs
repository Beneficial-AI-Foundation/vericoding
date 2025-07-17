// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(arr: Vec<int>, len: int) -> int
    reads arr
    requires
        arr.len() > 0 && 0 <= len <= arr.len()
{
    0
}

spec fn spec_SumArray(arr: Vec<int>) -> sum: int
    requires
        arr.len() > 0
    ensures
        sum == Sum(arr, arr.len())
;

proof fn lemma_SumArray(arr: Vec<int>) -> (sum: int)
    requires
        arr.len() > 0
    ensures
        sum == Sum(arr, arr.len())
{
    0
}

}