use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn suma_aux(V: &[int], i: int) -> int
    decreases V.len() - i
{
    if i >= V.len() {
        0
    } else {
        V[i] + suma_aux(V, i + 1)
    }
}

// Helper lemma to prove the relationship between suma_aux at different indices
proof fn suma_aux_step(V: &[int], i: int)
    requires 0 <= i < V.len()
    ensures suma_aux(V, i) == V[i] + suma_aux(V, i + 1)
{
    // This follows directly from the definition of suma_aux
}

// Lemma to prove the key invariant relationship
proof fn suma_aux_relation(V: &[int], i: int, sum: int)
    requires 
        0 <= i <= V.len(),
        sum == suma_aux(V, 0) - suma_aux(V, i)
    ensures 
        i < V.len() ==> sum + V[i] == suma_aux(V, 0) - suma_aux(V, i + 1)
{
    if i < V.len() {
        suma_aux_step(V, i);
        // suma_aux(V, i) == V[i] + suma_aux(V, i + 1)
        // sum == suma_aux(V, 0) - suma_aux(V, i)
        // sum == suma_aux(V, 0) - (V[i] + suma_aux(V, i + 1))
        // sum == suma_aux(V, 0) - V[i] - suma_aux(V, i + 1)
        // sum + V[i] == suma_aux(V, 0) - suma_aux(V, i + 1)
    }
}

fn suma_componentes(V: &[int]) -> (suma: int)
    ensures
        suma == suma_aux(V, 0)
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < V.len()
        invariant
            0 <= i <= V.len(),
            sum == suma_aux(V, 0) - suma_aux(V, i as int)
    {
        proof {
            suma_aux_relation(V, i as int, sum);
        }
        sum = sum + V[i];
        i = i + 1;
    }
    
    // At the end: sum == suma_aux(V, 0) - suma_aux(V, V.len())
    // Since suma_aux(V, V.len()) == 0, we have sum == suma_aux(V, 0)
    
    sum
}

}