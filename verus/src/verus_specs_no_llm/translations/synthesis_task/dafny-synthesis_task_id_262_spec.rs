// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SplitArray(arr: Vec<int>, L: int) -> firstPart: seq<int>, secondPart: seq<int>
    requires
        0 <= L <= arr.len()
    ensures
        firstPart.len() == L,
        secondPart.len() == arr.len() - L,
        firstPart + secondPart == arr.index(..)
;

proof fn lemma_SplitArray(arr: Vec<int>, L: int) -> (firstPart: Seq<int>, secondPart: Seq<int>)
    requires
        0 <= L <= arr.len()
    ensures
        firstPart.len() == L,
        secondPart.len() == arr.len() - L,
        firstPart + secondPart == arr.index(..)
{
    Seq::empty()
}

}