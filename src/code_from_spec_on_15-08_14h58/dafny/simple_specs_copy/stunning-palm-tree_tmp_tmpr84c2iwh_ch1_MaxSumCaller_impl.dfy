//ATOM

// Ex 1.7
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

//IMPL 
// look ma, no implementation!

method MaxSumCaller() {
  var sum, max := MaxSum(5, 3);
}