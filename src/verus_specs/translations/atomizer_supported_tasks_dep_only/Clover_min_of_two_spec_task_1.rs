pub fn Min(x: int, y: int) -> (z: int)
    ensures
        x <= y ==> z == x,
        x > y ==> z == y,
{
}