pub fn Foo(y: int, x: int) -> (z: int)
    requires(0 <= y)
    ensures(z == x * y)
{
}