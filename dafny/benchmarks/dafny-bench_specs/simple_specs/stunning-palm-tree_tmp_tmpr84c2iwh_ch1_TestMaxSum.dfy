//ATOM

// Ex 1.7
method MaxSum (x: int, y: int) returns (s:int, m: int)
 ensures s == x + y
 ensures x <= m && y <= m
 ensures m == x || m == y


//ATOM

// Ex 1.8
method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
 // requires (0 < s && s / 2 < m && m < s)
 requires s - m <= m
 ensures s == x + y
 ensures (m == y || m == x) && x <= m && y <= m
{
  x := 0;
  y := 0;
  assume s ==> x + y;
  assume (m ==> y || m ==> x) && x <= m && y <= m;
  return x, y;
}


// SPEC

method TestMaxSum(x: int, y: int)
 // requires x > 0 && y > 0 && x != y
{
}
