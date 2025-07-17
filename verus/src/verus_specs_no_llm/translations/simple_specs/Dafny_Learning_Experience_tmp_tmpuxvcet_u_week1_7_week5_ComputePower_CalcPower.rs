// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CalcPower(n: nat) -> p:nat
    ensures
        p == 2*n
;

proof fn lemma_CalcPower(n: nat) -> (p: nat)
    ensures
        p == 2*n
{
    0
}

}