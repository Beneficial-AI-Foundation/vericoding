// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn soma(a: Vec<nat>, i: nat) -> nat
    requires
        i <= a.len() //Tem que dizer que o i só vai até um valor antes do tamanho do array
  reads a //serve para dizer que está sendo lido da memoria o array a (áreas de memória)
{
    0
}

spec fn spec_somatorio(a: Vec<nat>) -> s:nat
    ensures
        s == soma(a, a.len())
;

proof fn lemma_somatorio(a: Vec<nat>) -> (s: nat)
    ensures
        s == soma(a, a.len())
{
    0
}

}