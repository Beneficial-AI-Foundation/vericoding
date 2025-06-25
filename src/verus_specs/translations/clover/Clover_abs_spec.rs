pub fn abs(x: int) -> (y: int)
    ensures(x >= 0 ==> x == y)
    ensures(x < 0 ==> x + y == 0)
{
}