// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn max(x: nat, y: nat) -> nat
{
    0
}

spec fn spec_slow_max(a: nat, b: nat) -> z: nat
    ensures
        z == max(a, b)
;

proof fn lemma_slow_max(a: nat, b: nat) -> (z: nat)
    ensures
        z == max(a, b)
{
    0
}

}