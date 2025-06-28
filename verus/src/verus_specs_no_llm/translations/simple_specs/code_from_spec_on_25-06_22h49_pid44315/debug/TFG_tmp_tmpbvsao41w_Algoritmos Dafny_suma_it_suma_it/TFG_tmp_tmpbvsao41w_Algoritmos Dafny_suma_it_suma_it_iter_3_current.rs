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
        assert(suma_vector(V, i) == 0);
        
        // Need to prove suma_hasta(V, V.len()) == suma_vector(V, 0)
        if V.len() == 0 {
            assert(suma_hasta(V, 0) == 0);
            assert(suma_vector(V, 0) == 0);
        } else {
            // suma_hasta(V, V.len()) == suma_vector(V, 0) by definition
            assert(suma_hasta(V, V.len()) == suma_vector(V, 0));
        }
    } else {
        // Inductive case
        lemma_suma_equivalence(V, i + 1);
        
        // We have: suma_hasta(V, i+1) + suma_vector(V, i+1) == suma_vector(V, 0)
        // We need: suma_hasta(V, i) + suma_vector(V, i) == suma_vector(V, 0)
        
        // By definition:
        // suma_hasta(V, i+1) = suma_hasta(V, i) + V[i]
        // suma_vector(V, i) = V[i] + suma_vector(V, i+1)
        
        assert(suma_hasta(V, i + 1) == suma_hasta(V, i) + V[i as int]);
        assert(suma_vector(V, i) == V[i as int] + suma_vector(V, i + 1));
        
        // So: (suma_hasta(V, i) + V[i]) + suma_vector(V, i+1) == suma_vector(V, 0)
        // Which gives us: suma_hasta(V, i) + (V[i] + suma_vector(V, i+1)) == suma_vector(V, 0)
        // Therefore: suma_hasta(V, i) + suma_vector(V, i) == suma_vector(V, 0)
    }
}

// Additional lemma to help with loop invariant maintenance
proof fn lemma_suma_hasta_step(V: Vec<int>, i: nat)
    requires i < V.len()
    ensures suma_hasta(V, i + 1) == suma_hasta(V, i) + V[i as int]
{
    // This follows directly from the definition of suma_hasta
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
            lemma_suma_hasta_step(V, i as nat);
        }
        sum = sum + V[i];
        i = i + 1;
    }
    
    proof {
        // At this point: sum == suma_hasta(V, V.len())
        // We need to prove: suma_hasta(V, V.len()) == suma_vector(V, 0)
        lemma_suma_equivalence(V, V.len() as nat);
        // This gives us: suma_hasta(V, V.len()) + suma_vector(V, V.len()) == suma_vector(V, 0)
        // Since suma_vector(V, V.len()) == 0, we get suma_hasta(V, V.len()) == suma_vector(V, 0)
        assert(suma_vector(V, V.len() as nat) == 0);
    }
    
    sum
}

}