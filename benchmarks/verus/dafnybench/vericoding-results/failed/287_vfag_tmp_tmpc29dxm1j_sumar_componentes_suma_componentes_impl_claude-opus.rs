use vstd::prelude::*;

verus! {

spec fn suma_aux(V: &[i32], n: int) -> int
    decreases V.len() - n
    when 0 <= n <= V.len()
{
    if n == V.len() {
        0
    } else {
        V[n as int] + suma_aux(V, n + 1)
    }
}

// <vc-helpers>
proof fn suma_aux_unfold(V: &[i32], n: int)
    requires 0 <= n < V.len()
    ensures suma_aux(V, n) == V[n as int] + suma_aux(V, n + 1)
{
    // This follows directly from the definition of suma_aux
}

proof fn suma_aux_base(V: &[i32], n: int)
    requires n == V.len()
    ensures suma_aux(V, n) == 0
{
    // This follows directly from the definition of suma_aux
}

proof fn suma_loop_equivalence(V: &[i32], i: int, suma_parcial: int)
    requires 
        0 <= i <= V.len(),
        suma_parcial == suma_aux(V, 0) - suma_aux(V, i),
    ensures suma_parcial + suma_aux(V, i) == suma_aux(V, 0)
{
    // This is a simple algebraic property
}
// </vc-helpers>

// <vc-spec>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
// </vc-spec>
// <vc-code>
{
    let mut suma: i32 = 0;
    let mut i: usize = 0;
    
    while i < V.len()
        invariant
            0 <= i <= V.len(),
            suma == suma_aux(V, 0) - suma_aux(V, i as int),
        decreases V.len() - i
    {
        proof {
            suma_aux_unfold(V, i as int);
        }
        suma = suma + V[i];
        i = i + 1;
    }
    
    proof {
        suma_aux_base(V, V.len() as int);
        suma_loop_equivalence(V, V.len() as int, suma as int);
    }
    
    suma
}
// </vc-code>

fn main() {}

}