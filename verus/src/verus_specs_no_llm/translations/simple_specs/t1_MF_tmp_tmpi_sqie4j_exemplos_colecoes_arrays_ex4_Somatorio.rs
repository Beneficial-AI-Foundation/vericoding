// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SomaAte(a: Vec<nat>, i: nat) -> nat
    requires
        0 <= i <= a.len()
 reads a
{
    0
}

spec fn spec_Somatorio(a: Vec<nat>) -> s:nat
    ensures
        s == SomaAte(a,a.len())
;

proof fn lemma_Somatorio(a: Vec<nat>) -> (s: nat)
    ensures
        s == SomaAte(a,a.len())
{
    0
}

}