pub fn Index(n: int) -> (i: int)
    requires(1 <= n)
    ensures(|i: int| 0 <= i < n)
{
}

pub fn Min(x: int, y: int) -> (m: int)
    ensures(|m: int| m <= x && m <= y)
    ensures(|m: int| m == x || m == y)
{
}

pub fn Max(x: int, y: int) -> (m: int)
{
}

pub fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures(|(s, m): (int, int)| s == x + y)
    ensures(|(s, m): (int, int)| m == if x >= y { x } else { y })
{
}

pub fn MaxSumCaller()
{
}

pub fn ReconstructFromMaxSum(s: int, m: int) -> (x: int, y: int)
    requires(s <= 2 * m)
    ensures(|(x, y): (int, int)| s == (x + y))
    ensures(|(x, y): (int, int)| (m == x || m == y) && x <= m && y <= m)
{
}

pub fn TestMaxSum(x: int, y: int)
{
}