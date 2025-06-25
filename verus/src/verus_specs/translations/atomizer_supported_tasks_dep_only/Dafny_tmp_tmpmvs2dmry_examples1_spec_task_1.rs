pub fn Abs(x: int) -> (y: int)
    requires()
    ensures(|y: int| y >= 0)
    ensures(|y: int| x >= 0 ==> x == y)
    ensures(|y: int| x < 0 ==> -x == y)
    ensures(|y: int| y == abs(x))
{
}

spec fn abs(x: int) -> int {
    if x > 0 { x } else { -x }
}