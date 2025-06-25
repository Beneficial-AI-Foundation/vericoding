pub fn Abs(x: int) -> (y: int)
    requires(x < 0)
    ensures(0 < y)
    ensures(y == -x)
{
}

pub fn Main()
{
}