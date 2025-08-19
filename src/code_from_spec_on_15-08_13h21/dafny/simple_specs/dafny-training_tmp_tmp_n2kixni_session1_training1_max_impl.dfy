//IMPL
method max(x: int, y: int) returns (m: int)
requires true
ensures true
{
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}