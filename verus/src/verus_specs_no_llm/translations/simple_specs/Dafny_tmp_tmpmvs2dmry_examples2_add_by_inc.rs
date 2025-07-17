// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_add_by_inc(x: nat, y: nat) -> z:nat
    ensures
        z == x+y
;

proof fn lemma_add_by_inc(x: nat, y: nat) -> (z: nat)
    ensures
        z == x+y
{
    0
}

}