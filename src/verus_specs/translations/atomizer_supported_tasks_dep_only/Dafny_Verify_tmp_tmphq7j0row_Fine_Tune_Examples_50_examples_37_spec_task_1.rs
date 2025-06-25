pub fn main(n: int) -> (x: int, m: int)
    requires(n > 0)
    ensures(|result: (int, int)| (n <= 0) || (0 <= result.1 && result.1 < n))
{
}