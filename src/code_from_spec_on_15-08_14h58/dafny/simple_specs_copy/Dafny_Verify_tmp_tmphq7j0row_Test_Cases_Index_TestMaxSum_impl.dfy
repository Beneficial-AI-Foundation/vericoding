method MaxSum(x: int, y: int) returns (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  /* code modified by LLM (iteration 1): Fixed assignment operations and removed assume statements */
  s := x + y;
  m := if x >= y then x else y;
}


//ATOM

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2 * m
  ensures s == (x + y)
  ensures (m == x || m == y) && x <= m && y <= m
{
  /* code modified by LLM (iteration 1): Implemented proper logic to reconstruct x and y from sum and max */
  y := s - m;
  x := m;
  // Check if this assignment satisfies the postcondition, if not swap
  if !(x <= m && y <= m) {
    x := s - m;
    y := m;
  }
}


//IMPL TestMaxSum

method TestMaxSum(x: int, y: int) 
{
  var s, m := MaxSum(x, y);
}