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

fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
{
    assume(false);
    unreached()
}

}
fn main() {}