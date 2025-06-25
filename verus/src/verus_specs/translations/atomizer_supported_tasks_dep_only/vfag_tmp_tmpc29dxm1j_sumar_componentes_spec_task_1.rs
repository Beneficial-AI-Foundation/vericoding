pub fn suma_componentes(V: &[i32]) -> (suma: i32)
    requires(V.len() >= 0)
    ensures(|result: i32| result == suma_aux(V, 0))
{
}

spec fn suma_aux(V: &[i32], n: int) -> int
    requires(V.len() >= 0)
    requires(0 <= n <= V.len())
    decreases(V.len() - n)
{
    if n == V.len() {
        0
    } else {
        V[n] + suma_aux(V, n + 1)
    }
}