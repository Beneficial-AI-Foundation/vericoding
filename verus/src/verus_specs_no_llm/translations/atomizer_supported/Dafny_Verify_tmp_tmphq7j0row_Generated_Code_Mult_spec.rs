// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_mult(a: int, b: int) -> x:int
    requires
        a >= 0 && b >= 0
    ensures
        x == a * b
;

proof fn lemma_mult(a: int, b: int) -> (x: int)
    requires
        a >= 0 && b >= 0
    ensures
        x == a * b
{
    0
}

}