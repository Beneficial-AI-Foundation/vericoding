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
proof fn lemma_suma_aux_len(V: &[i32], n: int)
    requires
        0 <= n <= V.len(),
    ensures
        suma_aux(V, n) == if n == V.len() { 0 } else { V[n as int] + suma_aux(V, n + 1) },
    decreases V.len() - n
{
    if n == V.len() {
    } else {
        lemma_suma_aux_len(V, n + 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < V.len()
        invariant
            0 <= i <= V.len(),
            sum == suma_aux(V, i as int),
        decreases V.len() - i
    {
        sum = sum + V[i];
        i = i + 1;
        proof {
            lemma_suma_aux_len(V, i as int);
        }
    }
    
    proof {
        lemma_suma_aux_len(V, 0);
    }
    
    sum
}
// </vc-code>

fn main() {}

}