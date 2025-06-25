pub fn abs(x: i32) -> (y: i32)
    ensures(0 <= y)
    ensures(x < 0 ==> y == -x)
    ensures(x >= 0 ==> y == x)
{
}