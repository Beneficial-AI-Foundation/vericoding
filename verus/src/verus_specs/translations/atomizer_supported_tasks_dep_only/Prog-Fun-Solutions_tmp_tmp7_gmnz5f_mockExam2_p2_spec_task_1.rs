pub fn problem2(p: int, q: int, X: int, Y: int) -> (r: int, s: int)
    requires(p == 2*X + Y && q == X + 3)
    ensures(|result: (int, int)| result.0 == X && result.1 == Y)
{
}