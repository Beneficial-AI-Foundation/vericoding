//IMPL 
method MaxSum(x:int, y:int) returns (s:int, m:int)
  ensures s == x+y
  ensures (m == x || m == y) && x <= m && y <= m
{
  s := x + y;
  if x >= y {
    m := x;
  } else {
    m := y;
  }
}