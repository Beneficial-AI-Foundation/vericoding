// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_div_ent_it(a: int, b: int) -> c: int, r: int)

// Algoritmo iterativo de la división de enteros
// que calcula su cociente y resto

    requires a >= 0 && b > 0
    ensures  a == b*c + r && 0 <= r < b
{
}


// SPEC 

method Main(
    requires
        a >= 0 && b > 0
    ensures
        a == b*c + r && 0 <= r < b
;

proof fn lemma_div_ent_it(a: int, b: int) -> (c: int, r: int)

// Algoritmo iterativo de la división de enteros
// que calcula su cociente y resto

    requires a >= 0 && b > 0
    ensures  a == b*c + r && 0 <= r < b
{
}


// SPEC 

method Main()
    requires
        a >= 0 && b > 0
    ensures
        a == b*c + r && 0 <= r < b
{
    (0, 0)
}

}