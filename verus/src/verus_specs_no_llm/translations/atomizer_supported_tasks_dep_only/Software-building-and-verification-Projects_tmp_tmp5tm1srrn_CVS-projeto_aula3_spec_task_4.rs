// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_maxArrayReverse(arr: Vec<int>) -> max: int
    requires
        arr.len() > 0
    ensures
        forall |i: int| 0 <= i < arr.len() ==> arr.index(i) <= max,
        exists |x: int|0 <= x < arr.len() && arr.index(x) == max
;

proof fn lemma_maxArrayReverse(arr: Vec<int>) -> (max: int)
    requires
        arr.len() > 0
    ensures
        forall |i: int| 0 <= i < arr.len() ==> arr.index(i) <= max,
        exists |x: int|0 <= x < arr.len() && arr.index(x) == max
{
    0
}

}