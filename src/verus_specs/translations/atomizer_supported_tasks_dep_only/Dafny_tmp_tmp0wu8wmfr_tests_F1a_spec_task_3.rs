pub fn Mid(p: int, q: int) -> (m: int)
    requires(p <= q)
    ensures(p <= m <= q)
    ensures(m - p <= q - m)
    ensures(0 <= (q - m) - (m - p) <= 1)
{
}