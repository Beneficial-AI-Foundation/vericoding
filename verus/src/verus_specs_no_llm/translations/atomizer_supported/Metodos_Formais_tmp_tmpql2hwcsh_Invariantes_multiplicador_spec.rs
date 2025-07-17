// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Mult(x: nat, y: nat) -> r:nat
    ensures
        r == x * y
;

proof fn lemma_Mult(x: nat, y: nat) -> (r: nat)
    ensures
        r == x * y
{
    0
}

}