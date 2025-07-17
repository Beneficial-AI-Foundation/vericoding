// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ComputeAvg(a: int, b: int) -> avg:int
    ensures
        avg == (a+b)/2
;

proof fn lemma_ComputeAvg(a: int, b: int) -> (avg: int)
    ensures
        avg == (a+b)/2
{
    0
}

}