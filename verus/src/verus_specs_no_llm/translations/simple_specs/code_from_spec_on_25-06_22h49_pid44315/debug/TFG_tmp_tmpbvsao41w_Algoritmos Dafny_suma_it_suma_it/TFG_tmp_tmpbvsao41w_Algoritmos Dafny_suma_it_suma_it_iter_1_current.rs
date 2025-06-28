use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to define the sum of a vector recursively
spec fn suma_vector(V: Vec<int>, start: nat) -> int
    decreases V.len() - start
{
    if start >= V.len() {
        0
    } else {
        V[start as int] + suma_vector(V, start + 1)
    }
}

fn suma_it(V: Vec<int>) -> (x: int)
// Algoritmo iterativo que calcula la
// suma de las componentes de un vector
    ensures x == suma_vector(V, 0)
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < V.len()
        invariant 
            0 <= i <= V.len(),
            sum == suma_vector(V, 0) - suma_vector(V, i as nat),
    {
        sum = sum + V[i];
        i = i + 1;
    }
    
    sum
}

}