pub fn Abs(x: int) -> (y: int)
    requires
        x == -1,
    ensures
        0 <= y,
        0 <= x ==> y == x,
        x < 0 ==> y == -x,
{
}

pub fn Abs2(x: real) -> (y: real)
    requires
        x == -0.5,
    ensures
        0.0 <= y,
        0.0 <= x ==> y == x,
        x < 0.0 ==> y == -x,
{
}

pub fn Main()
{
}