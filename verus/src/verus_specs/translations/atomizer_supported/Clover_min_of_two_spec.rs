pub fn Min(x: int, y: int) -> (z: int)
    ensures x <= y ==> z == x,
    ensures x > y ==> z == y,
{
}