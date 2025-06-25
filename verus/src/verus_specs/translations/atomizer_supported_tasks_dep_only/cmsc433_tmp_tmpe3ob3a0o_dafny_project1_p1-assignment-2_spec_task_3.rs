pub fn IntDiv(m: int, n: int) -> (d: int, r: int)
    requires(n > 0)
    ensures(|result: (int, int)| m == n * result.0 + result.1 && 0 <= result.1 && result.1 < n)
{
}