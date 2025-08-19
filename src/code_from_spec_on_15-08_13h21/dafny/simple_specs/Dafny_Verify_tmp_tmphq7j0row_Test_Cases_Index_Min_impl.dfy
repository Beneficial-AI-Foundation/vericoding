//IMPL 
method Min(x: int, y: int) returns (m: int) 
ensures m <= x && m <= y
ensures m == x || m == y
{
    if x <= y {
        m := x;
    } else {
        m := y;
    }
}