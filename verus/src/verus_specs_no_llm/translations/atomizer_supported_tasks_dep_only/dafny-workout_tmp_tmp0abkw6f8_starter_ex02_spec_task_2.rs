// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Abs(x: int) -> y: int
    requires
        x < 0
    ensures
        0 < y,
        y == -x
;

proof fn lemma_Abs(x: int) -> (y: int)
    requires
        x < 0
    ensures
        0 < y,
        y == -x
{
    0
}

}