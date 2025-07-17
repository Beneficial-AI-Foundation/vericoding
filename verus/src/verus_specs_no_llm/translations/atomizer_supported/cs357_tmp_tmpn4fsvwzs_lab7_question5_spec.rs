// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_M1(x: int, y: int) -> r: int
    ensures
        r == x*y
;

proof fn lemma_M1(x: int, y: int) -> (r: int)
    ensures
        r == x*y
{
    0
}

}