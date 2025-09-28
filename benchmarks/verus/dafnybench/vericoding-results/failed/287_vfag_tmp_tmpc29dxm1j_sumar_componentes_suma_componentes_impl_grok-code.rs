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
spec fn suma_aux(V: &[i32], n: int) -> int
    decreases (V.len() as int) - n
{
    recommends(0 <= n <= V.len() as int);
    if n == V.len() as int {
        0
    } else {
        V[n as usize] as int + suma_aux(V, n + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
// </vc-spec>
// <vc-code>
{
    let mut sum: int = 0;
    let mut i: int = 0;
    while i < V.len() as int
        invariant
            0 <= i <= V.len() as int,
            sum == suma_aux(V, 0) - suma_aux(V, i),
        decreases V.len() as int - i
    {
        sum = sum + V[i as usize] as int;
        i = i + 1;
    }
    sum as i32
}
// </vc-code>

fn main() {}

}