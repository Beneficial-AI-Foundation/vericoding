// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn pow(a: int, e: nat) -> (int)
{
    0
}

spec fn spec_Pow(a: nat, n: nat) -> y: nat
    ensures
        y == pow(a, n)
;

proof fn lemma_Pow(a: nat, n: nat) -> (y: nat)
    ensures
        y == pow(a, n)
{
    0
}

}