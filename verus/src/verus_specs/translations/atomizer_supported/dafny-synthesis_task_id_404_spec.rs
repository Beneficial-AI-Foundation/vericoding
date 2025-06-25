pub fn Min(a: int, b: int) -> (minValue: int)
    ensures(minValue == a || minValue == b)
    ensures(minValue <= a && minValue <= b)
{
}