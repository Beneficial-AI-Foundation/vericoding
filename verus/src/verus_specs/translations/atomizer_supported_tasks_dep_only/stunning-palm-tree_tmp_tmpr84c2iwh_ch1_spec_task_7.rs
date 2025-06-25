pub fn ReconstructFromMaxSum(s: int, m: int) -> (x: int, y: int)
    requires(s - m <= m)
    ensures(|result: (int, int)| s == result.0 + result.1)
    ensures(|result: (int, int)| (m == result.1 || m == result.0) && result.0 <= m && result.1 <= m)
{
}