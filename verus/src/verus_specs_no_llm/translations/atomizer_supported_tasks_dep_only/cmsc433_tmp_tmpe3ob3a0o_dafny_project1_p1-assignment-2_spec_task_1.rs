// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_PlusOne(x: int) -> y : int
    requires
        x >= 0
    ensures
        y > 0
;

proof fn lemma_PlusOne(x: int) -> (y: int)
    requires
        x >= 0
    ensures
        y > 0
{
    0
}

}