pub fn main(n: int) -> (i: int, x: int, y: int)
    requires(n >= 0)
    ensures(|result: (int, int, int)| (result.0 % 2 != 0) || (result.1 == 2 * result.2))
{
}