//ATOM

// Ex 1.7
method MaxSum (x: int, y: int) returns (s:int, m: int)
 ensures s == x + y
 ensures x <= m && y <= m
 ensures m == x || m == y
{
  /* code modified by LLM (iteration 1): moved ensures clauses before method body and added implementation */
  s := x + y;
  if x >= y {
    m := x;
  } else {
    m := y;
  }
}


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
  assume s == x + y;
  assume (m == y || m == x) && x <= m && y <= m;
  return x, y;
}


//IMPL TestMaxSum

method TestMaxSum(x: int, y: int)
 // requires x > 0 && y > 0 && x != y
{
  /* code modified by LLM (iteration 1): added precondition check and verification that reconstruction works */
  var s, m := MaxSum(x, y);
  
  // Check that the precondition for ReconstructFromMaxSum is satisfied
  assert s - m <= m; // This follows from s == x + y and m == max(x,y)
  
  var x2, y2 := ReconstructFromMaxSum(s, m);
  
  // Verify that reconstruction preserves the original relationship
  assert s == x2 + y2; // From ReconstructFromMaxSum postcondition
  assert (m == x2 || m == y2) && x2 <= m && y2 <= m; // From ReconstructFromMaxSum postcondition
}