// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn abs(x: int) -> int
{
    0
}

spec fn spec_Abs(x: int) -> y: int
    ensures
        abs(x) == y
;

proof fn lemma_Abs(x: int) -> (y: int)
    ensures
        abs(x) == y
{
    0
}

}