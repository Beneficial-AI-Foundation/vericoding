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
    } else if end <= V.len() {
        suma_hasta(V, end - 1) + V[(end - 1) as int]
    } else {
        suma_vector(V, 0)
    }
}

// Lemma to prove suma_hasta equals suma_vector from start
proof fn lemma_suma_hasta_eq_vector(V: Vec<int>, end: nat)
    requires end <= V.len()
    ensures suma_hasta(V, end) == suma_vector(V, 0) - suma_vector(V, end)
    decreases end
{
    if end == 0 {
        assert(suma_hasta(V, 0) == 0);
        assert(suma_vector(V, 0) - suma_vector(V, 0) == 0);
    } else {
        lemma_suma_hasta_eq_vector(V, end - 1);
        // suma_hasta(V, end-1) == suma_vector(V, 0) - suma_vector(V, end-1)
        // suma_hasta(V, end) == suma_hasta(V, end-1) + V[end-1]
        // suma_vector(V, end-1) == V[end-1] + suma_vector(V, end)
        // So suma_hasta(V, end) == suma_vector(V, 0) - suma_vector(V, end-1) + V[end-1]
        //                       == suma_vector(V, 0) - (V[end-1] + suma_vector(V, end)) + V[end-1]
        //                       == suma_vector(V, 0) - suma_vector(V, end)
    }
}

// Lemma to prove the main equivalence needed
proof fn lemma_suma_completa(V: Vec<int>)
    ensures suma_hasta(V, V.len() as nat) == suma_vector(V, 0)
{
    if V.len() == 0 {
        assert(suma_hasta(V, 0) == 0);
        assert(suma_vector(V, 0) == 0);
    } else {
        lemma_suma_hasta_eq_vector(V, V.len() as nat);
        // suma_hasta(V, V.len()) == suma_vector(V, 0) - suma_vector(V, V.len())
        // suma_vector(V, V.len()) == 0
        assert(suma_vector(V, V.len() as nat) == 0);
    }
}

// Helper lemma for the step in suma_hasta
proof fn lemma_suma_hasta_step(V: Vec<int>, i: nat)
    requires i < V.len()
    ensures suma_hasta(V, i + 1) == suma_hasta(V, i) + V[i as int]
{
    // This follows directly from the definition of suma_hasta
    assert(suma_hasta(V, i + 1) == suma_hasta(V, i) + V[i as int]);
}

fn suma_it(V: Vec<int>) -> (x: int)
// Algoritmo iterativo que calcula la
// suma de las componentes de un vector
    ensures x == suma_vector(V, 0)
{
    let mut sum = 0;
    let mut i: usize = 0;
    
    while i < V.len()
        invariant 
            0 <= i <= V.len(),
            sum == suma_hasta(V, i as nat),
    {
        proof {
            lemma_suma_hasta_step(V, i as nat);
        }
        sum = sum + V[i];
        i = i + 1;
    }
    
    proof {
        // At this point: sum == suma_hasta(V, V.len())
        // We need to prove: suma_hasta(V, V.len()) == suma_vector(V, 0)
        lemma_suma_completa(V);
    }
    
    sum
}

}