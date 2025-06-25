pub fn mroot3(n: int) -> (r: int)
    requires(n >= 0)
    ensures(|r: int| r >= 0 && r * r <= n < (r + 1) * (r + 1))
{
}