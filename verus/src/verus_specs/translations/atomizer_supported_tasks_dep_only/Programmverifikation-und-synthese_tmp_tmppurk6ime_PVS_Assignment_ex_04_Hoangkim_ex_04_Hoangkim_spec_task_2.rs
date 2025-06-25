pub fn intDiv(n: int, d: int) -> (q: int, r: int)
    requires(n >= d && n >= 0 && d > 0)
    ensures(|result: (int, int)| (d * result.0) + result.1 == n && 0 <= result.0 <= n/2 && 0 <= result.1 < d)
{
    todo!()
}