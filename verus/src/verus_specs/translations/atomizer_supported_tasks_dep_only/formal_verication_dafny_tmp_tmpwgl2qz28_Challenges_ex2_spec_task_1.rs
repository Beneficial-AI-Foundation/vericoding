pub fn Forbid42(x: int, y: int) -> (z: int)
    requires(y != 42)
    ensures(|z: int| z == x/(42-y))
{
}