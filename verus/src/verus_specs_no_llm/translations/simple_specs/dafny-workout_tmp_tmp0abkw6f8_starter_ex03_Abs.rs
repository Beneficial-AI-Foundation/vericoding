// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Abs(x: int) -> y: int
    requires
        x == -1
    ensures
        0 <= y,
        0 <= x ==> y == x,
        x < 0 ==> y == -x
;

proof fn lemma_Abs(x: int) -> (y: int)
    requires
        x == -1
    ensures
        0 <= y,
        0 <= x ==> y == x,
        x < 0 ==> y == -x
{
    0
}

}