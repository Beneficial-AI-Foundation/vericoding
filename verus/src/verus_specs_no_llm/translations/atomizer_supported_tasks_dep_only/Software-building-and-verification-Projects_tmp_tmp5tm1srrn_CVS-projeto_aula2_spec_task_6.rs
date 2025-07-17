// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_m2(x: nat) -> y: int
    requires
        x <= -1
    ensures
        y > x && y < x
;

proof fn lemma_m2(x: nat) -> (y: int)
    requires
        x <= -1
    ensures
        y > x && y < x
{
    0
}

}