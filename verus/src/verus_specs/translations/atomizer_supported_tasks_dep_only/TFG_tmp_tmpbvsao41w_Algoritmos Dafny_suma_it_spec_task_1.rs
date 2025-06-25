pub fn suma_it(V: &[i32]) -> (x: i32)
    ensures(x == suma_vector(V, 0))
{
}

pub fn suma_vector(V: &[i32], n: usize) -> i32
    requires(0 <= n && n <= V.len())
{
    if n == V.len() {
        0
    } else {
        V[n] + suma_vector(V, n + 1)
    }
}