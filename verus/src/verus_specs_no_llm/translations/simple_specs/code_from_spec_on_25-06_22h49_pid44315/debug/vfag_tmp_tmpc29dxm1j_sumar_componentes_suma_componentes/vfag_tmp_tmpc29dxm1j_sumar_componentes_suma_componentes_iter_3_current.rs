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
        V[i as usize] + suma_aux(V, i + 1)
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
        sum = sum + V[i];
        i = i + 1;
    }
    
    sum
}

}