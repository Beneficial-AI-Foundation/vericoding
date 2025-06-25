// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn div_ent_it(a: int, b: int) -> c: int, r: int)

// Algoritmo iterativo de la división de enteros
// que calcula su cociente y resto

    requires a >= 0 && b > 0
    ensures  a == b*c + r && 0 <= r < b
{
}


// SPEC 

method Main(
    requires a >= 0 and b > 0
    ensures a == b*c + r and 0 <= r < b
{
}

}