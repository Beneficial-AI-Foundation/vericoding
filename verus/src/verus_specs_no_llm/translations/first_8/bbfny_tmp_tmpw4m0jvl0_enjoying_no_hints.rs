// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn max(a: int, b: int) -> int
{}
//ATOM
method Testing'()
{
    0
}

spec fn spec_MultipleReturns(x: int, y: int) -> more: int, less: int
    requires
        0 < y
    ensures
        less < x < more
;

proof fn lemma_MultipleReturns(x: int, y: int) -> (more: int, less: int)
    requires
        0 < y
    ensures
        less < x < more
{
    (0, 0)
}

}