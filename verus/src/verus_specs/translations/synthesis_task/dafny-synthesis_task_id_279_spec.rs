pub fn NthDecagonalNumber(n: int) -> (decagonal: int)
    requires(n >= 0)
    ensures(|decagonal: int| decagonal == 4 * n * n - 3 * n)
{
}