// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Two(x: int) -> y: int
    ensures
        y == x + 1
;

proof fn lemma_Two(x: int) -> (y: int)
    ensures
        y == x + 1
{
    0
}

}