// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SwapSimultaneous(X: int, Y: int) -> x: int, y: int
    ensures
        x==Y,
        y==X
;

proof fn lemma_SwapSimultaneous(X: int, Y: int) -> (x: int, y: int)
    ensures
        x==Y,
        y==X
{
    (0, 0)
}

}