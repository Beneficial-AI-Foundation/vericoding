// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Main(xInit: int, y: int) -> z: int
    requires
        xInit >= 0,
        y >= 0
    ensures
        z == 0
;

proof fn lemma_Main(xInit: int, y: int) -> (z: int)
    requires
        xInit >= 0,
        y >= 0
    ensures
        z == 0
{
    0
}

}