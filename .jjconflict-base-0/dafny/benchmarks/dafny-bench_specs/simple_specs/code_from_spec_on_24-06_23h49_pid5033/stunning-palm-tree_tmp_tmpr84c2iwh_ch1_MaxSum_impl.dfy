//IMPL MaxSum
method MaxSum (x: int, y: int) returns (s:int, m: int)
 ensures s == x + y
 ensures x <= m && y <= m
 ensures m == x || m == y
{
    s := x + y;
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}