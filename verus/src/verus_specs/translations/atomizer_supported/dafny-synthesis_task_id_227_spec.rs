pub fn MinOfThree(a: int, b: int, c: int) -> (min: int)
    ensures(min <= a && min <= b && min <= c)
    ensures((min == a) || (min == b) || (min == c))
{
}