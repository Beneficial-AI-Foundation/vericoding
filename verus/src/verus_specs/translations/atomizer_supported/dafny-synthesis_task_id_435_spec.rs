pub fn last_digit(n: int) -> (d: int)
    requires n >= 0
    ensures 0 <= d < 10
    ensures n % 10 == d
{
}