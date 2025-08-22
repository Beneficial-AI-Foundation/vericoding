// Ex 1.3
//ATOM Triple
method Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  r := 3 * x;
}

//ATOM Caller
method Caller() returns (r: int)
  ensures r == 21
{
  r := Triple(7);
}

// Ex 1.6
//IMPL Min
method Min (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y 
{
  /* code modified by LLM (iteration 1): Simplified implementation with proper conditional logic */
  if x <= y {
    r := x;
  } else {
    r := y;
  }
}

//IMPL Min2
method Min2 (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y 
{
  /* code modified by LLM (iteration 1): Simplified implementation with proper conditional logic */
  if x <= y {
    r := x;
  } else {
    r := y;
  }
}

// Ex 1.7
//ATOM MaxSum
method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == x || m == y
  ensures m >= x && m >= y
{
  s := x + y;
  if x >= y {
    m := x;
  } else {
    m := y;
  }
}

//ATOM MaxSumCaller
method MaxSumCaller() returns (s: int, m: int)
  ensures s == 15
  ensures m == 10
{
  s, m := MaxSum(5, 10);
}

// Ex 1.8
//ATOM ReconstructFromMaxSum
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s >= 2 * m
  ensures x + y == s
  ensures (x == m || y == m)
  ensures x >= 0 && y >= 0
{
  if s == 2 * m {
    x := m;
    y := m;
  } else {
    x := m;
    y := s - m;
  }
}

//ATOM TestMaxSum
method TestMaxSum()
{
  var s, m := MaxSum(5, 10);
  var x, y := ReconstructFromMaxSum(s, m);
  assert x + y == 15;
  assert x == 10 || y == 10;
}

// Ex 1.9
//ATOM Average
method Average(x: int, y: int) returns (r: int)
  requires x >= 0 && y >= 0
  ensures 2 * r >= x + y
  ensures 2 * r <= x + y + 1
{
  r := (x + y) / 2;
}

//ATOM Triple'
method Triple'(x: int) returns (r: int)
  ensures r >= 3 * x
{
  r := 3 * x;
  if r < 3 * x {
    r := 3 * x;
  }
}