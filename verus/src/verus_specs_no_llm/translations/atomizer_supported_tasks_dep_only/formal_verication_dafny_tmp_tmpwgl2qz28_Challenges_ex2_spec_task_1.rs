// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Forbid42(x: int, y: int) -> z:int
    requires
        y != 42
    ensures
        z == x/(42-y)
;

proof fn lemma_Forbid42(x: int, y: int) -> (z: int)
    requires
        y != 42
    ensures
        z == x/(42-y)
{
    0
}

}