pub fn Forbid42(x: int, y: int) -> (z: int)
    requires(y != 42)
    ensures(z == x/(42-y))
{
}

pub fn Allow42(x: int, y: int) -> (z: int, err: bool)
    ensures(y != 42 ==> z == x/(42-y) && err == false)
    ensures(y == 42 ==> z == 0 && err == true)
{
}

pub fn TEST1()
{
}