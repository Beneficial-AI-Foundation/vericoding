pub fn main(n: int, k: int) -> (i: int, j: int)
    requires(n >= 0)
    requires(k == 1 || k >= 0)
    ensures(|result: (int, int)| k + result.0 + result.1 >= 2 * n)
{
}