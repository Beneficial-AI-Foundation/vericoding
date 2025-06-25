pub fn main(x: int) -> (j: int, i: int)
    requires(x > 0)
    ensures(|result: (int, int)| result.0 == 2 * x)
{
}