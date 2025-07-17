// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Swap(a: int, b: int) -> result: seq<int>
    ensures
        result.len() == 2,
        result.index(0) == b,
        result.index(1) == a
;

proof fn lemma_Swap(a: int, b: int) -> (result: Seq<int>)
    ensures
        result.len() == 2,
        result.index(0) == b,
        result.index(1) == a
{
    Seq::empty()
}

}