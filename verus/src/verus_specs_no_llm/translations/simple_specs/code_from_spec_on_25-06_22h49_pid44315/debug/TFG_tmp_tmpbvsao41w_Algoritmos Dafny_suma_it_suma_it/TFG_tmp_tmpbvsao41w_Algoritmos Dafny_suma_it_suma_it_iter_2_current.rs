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

// Helper spec function to define sum from 0 to end (exclusive)
spec fn suma_hasta(V: Vec<int>, end: nat) -> int
    decreases end
{
    if end == 0 {
        0
    } else if end > V.len() {
        suma_vector(V, 0)
    } else {
        suma_hasta(V, (end - 1) as nat) + V[(end - 1) as int]
    }
}

// Lemma to relate suma_hasta and suma_vector
proof fn lemma_suma_equivalence(V: Vec<int>, i: nat)
    requires i <= V.len()
    ensures suma_hasta(V, i) + suma_vector(V, i) == suma_vector(V, 0)
    decreases V.len() - i
{
    if i >= V.len() {
        // Base case: suma_hasta(V, V.len()) == suma_vector(V, 0)
        // and suma_vector(V, V.len()) == 0
    } else {
        // Inductive case
        lemma_suma_equivalence(V, i + 1);
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
            sum == suma_hasta(V, i as nat),
    {
        proof {
            lemma_suma_equivalence(V, i as nat);
        }
        sum = sum + V[i];
        i = i + 1;
    }
    
    proof {
        lemma_suma_equivalence(V, V.len() as nat);
    }
    
    sum
}

}