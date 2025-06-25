pub fn Max(x: int, y: int) -> (a: int)
    ensures
        a == x || a == y,
        x > y ==> a == x,
        x <= y ==> a == y,
{
}