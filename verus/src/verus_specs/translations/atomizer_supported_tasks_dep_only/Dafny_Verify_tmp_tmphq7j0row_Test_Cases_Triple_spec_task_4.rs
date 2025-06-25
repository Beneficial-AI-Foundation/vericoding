pub fn TripleConditions(x: int) -> (r: int)
    requires(x % 2 == 0)
    ensures(r == 3 * x)
{
}