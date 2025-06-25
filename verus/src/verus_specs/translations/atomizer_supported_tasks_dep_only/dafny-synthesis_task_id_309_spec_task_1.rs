pub fn Max(a: int, b: int) -> (maxValue: int)
    ensures(maxValue == a || maxValue == b)
    ensures(maxValue >= a && maxValue >= b)
{
}