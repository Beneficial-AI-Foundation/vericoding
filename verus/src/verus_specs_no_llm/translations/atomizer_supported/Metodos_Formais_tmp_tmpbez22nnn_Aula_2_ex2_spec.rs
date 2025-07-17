// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Potencia(x: nat, y: nat) -> nat
{
    0
}

spec fn spec_Pot(x: nat, y: nat) -> r: nat
    ensures
        r == Potencia(x,y)
;

proof fn lemma_Pot(x: nat, y: nat) -> (r: nat)
    ensures
        r == Potencia(x,y)
{
    0
}

}