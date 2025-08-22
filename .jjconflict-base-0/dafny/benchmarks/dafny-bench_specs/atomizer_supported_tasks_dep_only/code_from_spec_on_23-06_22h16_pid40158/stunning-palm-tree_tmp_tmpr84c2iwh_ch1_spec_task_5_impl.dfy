// Ex 1.3
//ATOM Triple
method Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  r := 3 * x;
}

//ATOM Caller
method Caller()
{
  var t := Triple(18);
  assert t < 100;
}

// Ex 1.6
//ATOM MinUnderSpec
method MinUnderSpec(x: int, y: int) returns (z: int)
  ensures z <= x && z <= y
{
  z := if x <= y then x else y;
}

//ATOM Min
method Min(x: int, y: int) returns (z: int)
  ensures z <= x && z <= y
  ensures z == x || z == y
{
  if x <= y {
    z := x;
  } else {
    z := y;
  }
}

// Ex 1.7
//IMPL MaxSum
method MaxSum(x: int, y: int) returns (s: int, m: int)
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

// Ex 1.8
//ATOM ReconstructFromMaxSum
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2 * m
  ensures x + y == s
  ensures (x <= m && y <= m) && (x == m || y == m)
{
  x := m;
  y := s - m;
}

//ATOM TestMaxSum
method TestMaxSum()
{
  var s, m := MaxSum(3, 2);
  var x, y := ReconstructFromMaxSum(s, m);
  assert (x == 3 && y == 2) || (x == 2 && y == 3);
}

// Ex 1.9
//ATOM Average
method Average(a: int, b: int) returns (x: int)
  requires a <= b
  ensures a <= x <= b
{
  x := (a + b) / 2;
}

//ATOM Triple'
method Triple'(x: int) returns (r: int)
  ensures r == 3 * x
{
  var y := 2 * x;
  r := x + y;
}