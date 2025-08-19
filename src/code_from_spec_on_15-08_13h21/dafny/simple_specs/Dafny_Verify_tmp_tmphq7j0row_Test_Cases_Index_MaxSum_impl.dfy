//IMPL 
method MaxSum(x: int, y: int) returns (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
    s := x + y;
    m := if x >= y then x else y;
}