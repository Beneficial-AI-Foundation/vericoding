//ATOM
method MaxSum(x: int, y: int) returns (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  /* code modified by LLM (iteration 1): Replaced assume statements with actual implementation */
  s := x + y;
  m := if x >= y then x else y;
}

//ATOM
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2 * m
  ensures s == (x + y)
  ensures (m == x || m == y) && x <= m && y <= m
{
  /* code modified by LLM (iteration 1): Replaced assume statements with actual implementation */
  x := m;
  y := s - m;
}

//IMPL TestMaxSum
method TestMaxSum(x: int, y: int) 
{
  var s, m := MaxSum(x, y);
  
  /* code modified by LLM (iteration 1): Added assertion to help verification understand the relationship between s, m, x, y */
  assert s == x + y;
  assert m == if x >= y then x else y;
  
  if s <= 2 * m {
    var x2, y2 := ReconstructFromMaxSum(s, m);
    assert s == x2 + y2;
    assert (m == x2 || m == y2) && x2 <= m && y2 <= m;
  }
}