pub fn multiple_returns(x: int, y: int) -> (more: int, less: int)
    ensures(|result: (int, int)| result.0 == x + y),
    ensures(|result: (int, int)| result.1 == x - y),
{
}