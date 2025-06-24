// IMPL 
method Index(n: int) returns (i: int) 
requires 1 <= n
ensures 0 <= i < n
{
    i := 0;
}


// IMPL 
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


// IMPL 
method Max(x: int, y: int) returns (m: int) {
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}


// IMPL 
method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
    s := x + y;
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}


// IMPL 
method MaxSumCaller() {
    var s, m := MaxSum(5, 3);
}


// IMPL 
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s <= 2 * m
    ensures s == (x + y)
    ensures (m == x || m == y) && x <= m && y <= m
{
    x := m;
    y := s - m;
}


// IMPL 
method TestMaxSum(x: int, y: int) 
{
    var s, m := MaxSum(x, y);
    var x_reconstructed, y_reconstructed := ReconstructFromMaxSum(s, m);
}