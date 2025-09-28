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
proof fn lemma_suma_aux_nonnegative_seq_bound(V: &[i32], n: int)
    requires
        0 <= n <= V.len(),
    ensures
        suma_aux(V, n) == if n == V.len() { 0 } else { V[n] + suma_aux(V, n + 1) },
    decreases V.len() - n
{
    reveal(suma_aux);
}

proof fn lemma_suma_aux_zero_when_n_equals_len(V: &[i32], n: int)
    requires
        n == V.len(),
    ensures
        suma_aux(V, n) == 0,
{
    reveal(suma_aux);
}

proof fn lemma_suma_aux_recursive(V: &[i32], n: int)
    requires
        0 <= n < V.len(),
    ensures
        suma_aux(V, n) == V[n] + suma_aux(V, n + 1),
{
    reveal(suma_aux);
}

spec fn seq_sum(s: Seq<i32>, idx: int) -> int
    recommends 0 <= idx <= s.len()
    decreases s.len() - idx
{
    if idx == s.len() {
        0
    } else {
        s[idx] + seq_sum(s, idx + 1)
    }
}

proof fn lemma_suma_aux_equals_seq_sum(V: &[i32], n: int)
    requires 0 <= n <= V.len(),
    ensures suma_aux(V, n) == seq_sum(V@, n),
    decreases V.len() - n
{
    reveal(suma_aux);
    if n < V.len() {
        lemma_suma_aux_equals_seq_sum(V, n + 1);
    }
}

proof fn lemma_seq_sum_empty(s: Seq<i32>)
    requires true,
    ensures seq_sum(s, s.len()) == 0
{
}

proof fn lemma_seq_sum_step(s: Seq<i32>, n: int)
    requires 0 <= n < s.len(),
    ensures seq_sum(s, n) == s[n] + seq_sum(s, n + 1)
{
}

proof fn lemma_sum_nonnegative(s: Seq<i32>, idx: int)
    requires 0 <= idx <= s.len(),
    ensures 0 <= seq_sum(s, idx),
    decreases s.len() - idx
{
    if idx < s.len() {
        lemma_sum_nonnegative(s, idx + 1);
    }
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
            suma == seq_sum(V@, i as int),
        decreases V.len() - i
    {
        assert(0 <= i < V.len()) by { lemma_sum_nonnegative(V@, (i + 1) as int); }
        proof { lemma_seq_sum_step(V@, i as int); }
        suma = (suma + V[i]) as i32;
        i = i + 1;
    }
    
    proof {
        lemma_suma_aux_equals_seq_sum(V, 0);
    }
    suma
}
// </vc-code>

fn main() {}

}