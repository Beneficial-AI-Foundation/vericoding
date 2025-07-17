// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_m1(x: int, y: int) -> z: int
    requires
        0 < x < y
    ensures
        z >= 0 && z < y && z != x
;

proof fn lemma_m1(x: int, y: int) -> (z: int)
    requires
        0 < x < y
    ensures
        z >= 0 && z < y && z != x
{
    0
}

}