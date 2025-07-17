// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_max(a: int, b: int) -> z: int
    requires
        true
    ensures
        z >= a || z >= b
;

proof fn lemma_max(a: int, b: int) -> (z: int)
    requires
        true
    ensures
        z >= a || z >= b
{
    0
}

}