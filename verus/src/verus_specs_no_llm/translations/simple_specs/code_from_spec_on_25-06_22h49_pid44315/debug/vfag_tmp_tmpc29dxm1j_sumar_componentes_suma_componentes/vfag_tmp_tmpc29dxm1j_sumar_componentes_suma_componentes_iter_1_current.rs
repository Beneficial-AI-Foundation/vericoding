// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn suma_aux(V: array<int>, i: int) -> int
    decreases V.len() - i
{
    if i >= V.len() {
        0
    } else {
        V.spec_index(i) + suma_aux(V, i + 1)
    }
}

fn suma_componentes(V: array<int>) -> (suma: int)
    ensures
        suma == suma_aux(V, 0)
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < V.len()
        invariant
            0 <= i <= V.len(),
            sum == suma_aux(V, 0) - suma_aux(V, i)
    {
        sum = sum + V[i];
        i = i + 1;
    }
    
    sum
}

}