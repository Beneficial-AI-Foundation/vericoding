// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No logical change needed; the error was at the call site. */
proof fn suma_aux_unfold(V: &[i32], n: int)
    requires 0 <= n < V.len()
    ensures suma_aux(V, n) == V[n as int] + suma_aux(V, n + 1)
{ }
// </vc-helpers>

// <vc-spec>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by moving the ghost function call into a proof block. */
    let mut suma: i64 = 0;
    let mut i: usize = 0;
    while i < V.len()
        invariant
            0 <= i <= V.len(),
            suma as int + suma_aux(V, i as int) == suma_aux(V, 0),
        decreases V.len() - i
    {
        proof {
            suma_aux_unfold(V, i as int);
        }
        suma = suma + (V[i] as i64);
        i = i + 1;
    }
    suma as i32
}
// </vc-code>

}
fn main() {}