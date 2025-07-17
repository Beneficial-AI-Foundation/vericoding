// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn suma_vector(V: Vec<int>, n: nat) -> int

// x = V[n] + V[n + 1] + ... + V[N - 1]
// Funcion auxiliar para la suma de
// las componentes de un vector
    requires
        0 <= n <= V.len()  
    reads V
{
    0
}

spec fn spec_suma_it(V: Vec<int>) -> x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

    ensures  x == suma_vector(V, 0
    ensures
        x == suma_vector(V, 0)
;

proof fn lemma_suma_it(V: Vec<int>) -> (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

    ensures  x == suma_vector(V, 0)
    ensures
        x == suma_vector(V, 0)
{
    (0, 0)
}

}