// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_q(x: nat, y: nat) -> z:nat
    requires
        y - x > 2
    ensures
        x < z*z < y


// SPEC

method strange(),
        1==2
;

proof fn lemma_q(x: nat, y: nat) -> (z: nat)
    requires
        y - x > 2
    ensures
        x < z*z < y


// SPEC

method strange(),
        1==2
{
    0
}

}