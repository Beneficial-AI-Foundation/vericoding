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
proof fn suma_aux_recursive_step(V: &[i32], n: int)
    requires 0 <= n < V.len()
    ensures suma_aux(V, n) == V[n as int] + suma_aux(V, n+1)
{
    reveal_with_fuel(suma_aux, 1);
}

proof fn suma_aux_sum(V: &[i32], n: int, m: int)
    requires 0 <= n <= m <= V.len()
    ensures suma_aux(V, n) - suma_aux(V, m) == (n..m).sum_by(|k| V[k as int])
{
    if n == m { }
    else {
        suma_aux_recursive_step(V, n);
        assert(suma_aux(V, n) - suma_aux(V, m) == V[n] + (suma_aux(V, n+1) - suma_aux(V, m)));
        suma_aux_sum(V, n+1, m);
    }
}

proof fn suma_aux_zero(V: &[i32])
    ensures suma_aux(V, V.len() as int) == 0
{
    reveal_with_fuel(suma_aux, 1);
}
// </vc-helpers>

// <vc-spec>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
// </vc-spec>
// <vc-code>
{
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < V.len()
        invariant 0 <= i as int <= V.len() as int
        invariant total == suma_aux(V, 0) - suma_aux(V, i as int)
    {
        proof {
            suma_aux_recursive_step(V, i as int);
        }
        total = total + V[i];
        i = i + 1;
    }
    proof {
        suma_aux_zero(V);
    }
    total
}
// </vc-code>

fn main() {}

}