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


//ATOM

// Ex 1.8
method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
 // requires (0 < s && s / 2 < m && m < s)
 requires s - m <= m
 ensures s == x + y
 ensures (m == y || m == x) && x <= m && y <= m
{
  x := s - m;
  y := m;
}


//IMPL 

method TestMaxSum(x: int, y: int)
 // requires x > 0 && y > 0 && x != y
{
  /* code modified by LLM (iteration 1): Added method calls with proper verification flow */
  var s, m := MaxSum(x, y);
  
  /* code modified by LLM (iteration 1): Added precondition check before calling ReconstructFromMaxSum */
  if s - m <= m {
    var x', y' := ReconstructFromMaxSum(s, m);
    
    /* code modified by LLM (iteration 1): Added assertions to verify the reconstruction properties */
    assert s == x' + y';
    assert (m == x' || m == y') && x' <= m && y' <= m;
    
    /* code modified by LLM (iteration 1): Added verification that original sum and max are preserved */
    assert s == x + y; // from MaxSum postcondition
    assert x <= m && y <= m; // from MaxSum postcondition
    assert m == x || m == y; // from MaxSum postcondition
  }
}