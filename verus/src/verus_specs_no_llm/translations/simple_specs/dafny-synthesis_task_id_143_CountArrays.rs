// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CountArrays(arrays: Seq<Vec<int>>) -> count: int
    ensures
        count >= 0,
        count == arrays.len()
;

proof fn lemma_CountArrays(arrays: Seq<Vec<int>>) -> (count: int)
    ensures
        count >= 0,
        count == arrays.len()
{
    0
}

}