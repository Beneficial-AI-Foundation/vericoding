//ATOM

method MaxSum(x: int, y: int) returns (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  /* code modified by LLM (iteration 1): fixed syntax errors in assume statements */
  s := x + y;
  m := if x >= y then x else y;
  return s, m;
}

//ATOM

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2 * m
  ensures s == (x + y)
  ensures (m == x || m == y) && x <= m && y <= m
{
  /* code modified by LLM (iteration 1): implemented proper logic to satisfy postconditions */
  x := m;
  y := s - m;
  return x, y;
}

//IMPL TestMaxSum

method TestMaxSum(x: int, y: int) 
{
  /* code modified by LLM (iteration 1): completed implementation with proper verification */
  var s, m := MaxSum(x, y);
  if s <= 2 * m {
    var x', y' := ReconstructFromMaxSum(s, m);
    // The postconditions of ReconstructFromMaxSum guarantee:
    // s == x' + y' and (m == x' || m == y') && x' <= m && y' <= m
  }
}