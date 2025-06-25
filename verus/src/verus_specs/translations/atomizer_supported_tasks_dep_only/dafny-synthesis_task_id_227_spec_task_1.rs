pub fn min_of_three(a: int, b: int, c: int) -> (min: int)
    ensures(min <= a && min <= b && min <= c)
    ensures((min == a) || (min == b) || (min == c))
{
}