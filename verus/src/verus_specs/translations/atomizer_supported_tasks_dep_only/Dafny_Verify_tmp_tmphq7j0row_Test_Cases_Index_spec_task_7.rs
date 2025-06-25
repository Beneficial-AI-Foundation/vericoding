pub fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures(s == x + y)
    ensures(m == if x >= y { x } else { y })
{
}

pub fn ReconstructFromMaxSum(s: int, m: int) -> (x: int, y: int)
    requires(s <= 2 * m)
    ensures(s == (x + y))
    ensures((m == x || m == y) && x <= m && y <= m)
{
}

pub fn TestMaxSum(x: int, y: int)
{
}