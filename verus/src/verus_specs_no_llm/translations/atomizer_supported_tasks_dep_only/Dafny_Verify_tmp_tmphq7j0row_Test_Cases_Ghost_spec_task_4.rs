// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MyMethod(x: int) -> y: int
    requires
        10 <= x
    ensures
        25 <= y
;

proof fn lemma_MyMethod(x: int) -> (y: int)
    requires
        10 <= x
    ensures
        25 <= y
{
    0
}

}