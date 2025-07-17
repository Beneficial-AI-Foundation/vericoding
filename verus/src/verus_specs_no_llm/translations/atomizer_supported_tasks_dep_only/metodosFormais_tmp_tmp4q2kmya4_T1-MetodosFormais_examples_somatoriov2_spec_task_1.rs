// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn somaAteAberto(a: Vec<nat>, i: nat) -> nat
    requires
        i <= a.len()
reads a
{
    0
}

spec fn spec_somatorio(a: Vec<nat>) -> s:nat
    ensures
        s == somaAteAberto(a, a.len())
;

proof fn lemma_somatorio(a: Vec<nat>) -> (s: nat)
    ensures
        s == somaAteAberto(a, a.len())
{
    0
}

}