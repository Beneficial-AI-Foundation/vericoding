pub fn multipleReturns(x: int, y: int) -> (more: int, less: int)
    requires(y > 0)
    ensures(|result: (int, int)| result.1 < x < result.0)
{
}