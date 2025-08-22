//ATOM

method MaxSum(x: int, y: int) returns (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  s := 0;
  m := 0;
  assume s == x + y;
  assume m == if x >= y then x else y;
  return s, m;
}

//ATOM

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2 * m
  ensures s == (x + y)
  ensures (m == x || m == y) && x <= m && y <= m
{
  x := 0;
  y := 0;
  assume s == (x + y);
  assume (m == x || m == y) && x <= m && y <= m;
  return x, y;
}

//IMPL TestMaxSum

method TestMaxSum(x: int, y: int) 
{
  var s, m := MaxSum(x, y);
  var x_reconstructed, y_reconstructed := ReconstructFromMaxSum(s, m);
}