pub fn main(n: int) -> (a: int, b: int)
    requires(n >= 0)
    ensures(|result: (int, int)| result.0 + result.1 == 3 * n)
{
}