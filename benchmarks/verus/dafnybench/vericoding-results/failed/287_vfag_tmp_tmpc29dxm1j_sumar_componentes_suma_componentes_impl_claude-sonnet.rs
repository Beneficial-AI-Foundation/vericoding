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
proof fn suma_aux_shift_lemma(V: &[i32], n: int)
    requires 0 <= n < V.len()
    ensures suma_aux(V, n) == V[n] + suma_aux(V, n + 1)
    decreases V.len() - n
{
    // This follows directly from the definition of suma_aux
}

proof fn suma_aux_base_lemma(V: &[i32])
    requires V.len() >= 0
    ensures suma_aux(V, V.len() as int) == 0
{
    // This follows directly from the definition of suma_aux
}

proof fn suma_aux_difference_lemma(V: &[i32], i: int)
    requires 0 <= i < V.len()
    ensures suma_aux(V, i) == V[i] + suma_aux(V, i + 1)
{
    suma_aux_shift_lemma(V, i);
}
// </vc-helpers>

// <vc-spec>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
// </vc-spec>
// <vc-code>
{
    let mut suma = 0i32;
    let mut i = 0;
    
    while i < V.len()
        invariant 
            0 <= i <= V.len(),
            suma == suma_aux(V, 0) - suma_aux(V, i as int),
            suma_aux(V, 0) <= i32::MAX,
            suma_aux(V, 0) >= i32::MIN,
            suma >= i32::MIN,
            suma <= i32::MAX
        decreases V.len() - i
    {
        proof {
            suma_aux_difference_lemma(V, i as int);
            assert(suma_aux(V, i as int) == V[i as int] + suma_aux(V, i as int + 1));
            assert(suma_aux(V, 0) - suma_aux(V, i as int + 1) == suma_aux(V, 0) - suma_aux(V, i as int) + V[i as int]);
        }
        
        suma = suma + V[i];
        i = i + 1;
    }
    
    proof {
        suma_aux_base_lemma(V);
        assert(suma_aux(V, V.len() as int) == 0);
        assert(suma == suma_aux(V, 0) - suma_aux(V, V.len() as int));
        assert(suma == suma_aux(V, 0) - 0);
        assert(suma == suma_aux(V, 0));
    }
    
    suma
}
// </vc-code>

fn main() {}

}