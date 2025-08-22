// Ex 1.3
//ATOM_PLACEHOLDER_Triple

//ATOM_PLACEHOLDER_Caller

// Ex 1.6
//ATOM_PLACEHOLDER_MinUnderSpec

//ATOM_PLACEHOLDER_Min

// Ex 1.7
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

// Ex 1.8
//IMPL ReconstructFromMaxSum
method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
  requires s - m <= m
  ensures s == x + y
  ensures (m == y || m == x) && x <= m && y <= m
{
  x := m;
  y := s - m;
}

//IMPL TestMaxSum
method TestMaxSum(x: int, y: int)
{
  var s, m := MaxSum(x, y);
  var x', y' := ReconstructFromMaxSum(s, m);
}

// Ex 1.9
//ATOM_PLACEHOLDER_Average

//ATOM_PLACEHOLDER_Triple'