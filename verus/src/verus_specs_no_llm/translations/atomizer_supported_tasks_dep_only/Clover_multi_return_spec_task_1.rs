// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MultipleReturns(x: int, y: int) -> more: int, less: int
    ensures
        more == x+y,
        less == x-y
;

proof fn lemma_MultipleReturns(x: int, y: int) -> (more: int, less: int)
    ensures
        more == x+y,
        less == x-y
{
    (0, 0)
}

}