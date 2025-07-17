// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MultiReturn(x: int, y: int) -> more:int, less:int
    requires
        y>=0
    ensures
        less <= x <= more
;

proof fn lemma_MultiReturn(x: int, y: int) -> (more: int, less: int)
    requires
        y>=0
    ensures
        less <= x <= more
{
    (0, 0)
}

}