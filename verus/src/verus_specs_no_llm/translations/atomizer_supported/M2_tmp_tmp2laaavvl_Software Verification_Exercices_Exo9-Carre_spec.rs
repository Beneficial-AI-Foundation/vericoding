// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Carre(a: nat) -> c: nat
    ensures
        c == a*a
;

proof fn lemma_Carre(a: nat) -> (c: nat)
    ensures
        c == a*a
{
    0
}

}