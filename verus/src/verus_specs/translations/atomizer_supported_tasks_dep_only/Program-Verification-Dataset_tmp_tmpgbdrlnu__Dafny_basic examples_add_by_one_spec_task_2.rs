pub fn bar(x: i32, y: i32) -> (r: i32)
    requires
        y >= 0,
    ensures
        r == x + y,
{
}