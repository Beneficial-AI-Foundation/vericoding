pub fn Abs(x: int) -> (y: int)
    ensures
        y >= 0,
        x >= 0 ==> x == y,
        x < 0 ==> -x == y,
        y == abs(x),
{
}

spec fn abs(x: int) -> int {
    if x > 0 { x } else { -x }
}

pub fn Testing() {
}

pub fn MultiReturn(x: int, y: int) -> (more: int, less: int)
    requires
        y >= 0,
    ensures
        less <= x <= more,
{
}

pub fn Max(x: int, y: int) -> (a: int)
    ensures
        a == x || a == y,
        x > y ==> a == x,
        x <= y ==> a == y,
{
}