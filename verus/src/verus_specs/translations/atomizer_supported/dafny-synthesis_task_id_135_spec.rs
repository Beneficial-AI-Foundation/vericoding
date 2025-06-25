pub fn nth_hexagonal_number(n: int) -> (hexNum: int)
    requires n >= 0
    ensures hexNum == n * ((2 * n) - 1)
{
}