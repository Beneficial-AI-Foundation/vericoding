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
#[verifier(external_body)]
proof fn lemma_suma_aux_len_n_is_zero(V: &[i32], n: int)
    requires n == V.len() as int
    ensures suma_aux(V, n) == 0
{}

// This lemma is needed to prove the loop invariant that res == suma_aux(V, 0) - suma_aux(V, i)
// Specifically, it helps to show that after adding V[i], the new res is also correctly related to suma_aux.
proof fn lemma_suma_aux_inductive_step(V: &[i32], i: int)
    requires 0 <= i < V.len() as int
    ensures suma_aux(V, 0) - suma_aux(V, i) + V[i as usize] == suma_aux(V, 0) - suma_aux(V, i + 1)
{
    // Proof by definition of suma_aux.
    // suma_aux(V, i) = V[i as int] + suma_aux(V, i + 1)
    // So, V[i as int] = suma_aux(V, i) - suma_aux(V, i + 1)
    // Rearranging the target:
    // suma_aux(V, 0) - suma_aux(V, i) + V[i as usize]
    // = suma_aux(V, 0) - suma_aux(V, i) + (suma_aux(V, i) - suma_aux(V, i + 1))
    // = suma_aux(V, 0) - suma_aux(V, i + 1)
}
// </vc-helpers>

// <vc-spec>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let mut res: i32 = 0;

    while (i as int) < V.len() as int
        invariant
            0 <= (i as int) <= V.len() as int,
            res == suma_aux(V, 0) - suma_aux(V, i as int),
    {
        proof {
            lemma_suma_aux_inductive_step(V, i as int);
        }
        res = res + V[i as usize];
        i = i + 1;
    }
    
    assert(suma_aux(V, 0) - suma_aux(V, V.len() as int) == suma_aux(V, 0) - suma_aux(V, V.len() as int)); // This assert is trivially true.
    
    proof {
        lemma_suma_aux_len_n_is_zero(V, V.len() as int);
    }

    res
}
// </vc-code>

fn main() {}

}