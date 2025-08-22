//ATOM_PLACEHOLDER_Index

//ATOM_PLACEHOLDER_Min

//ATOM_PLACEHOLDER_Max

//IMPL MaxSum
/* code modified by LLM (iteration 1): removed duplicate method definition */
method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
  s := x + y;
  m := if x >= y then x else y;
}

//IMPL ReconstructFromMaxSum
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s <= 2 * m
    ensures s == (x + y)
    ensures (m == x || m == y) && x <= m && y <= m
{
  /* code modified by LLM (iteration 1): added logic to ensure m is actually the maximum of x and y */
  if s <= m {
    x := s;
    y := 0;
    if s < m {
      x := m;
      y := s - m;
    }
  } else {
    x := m;
    y := s - m;
  }
  
  /* code modified by LLM (iteration 1): added assertion to help verification */
  assert x + y == s;
  assert x <= m && y <= m;
  
  /* code modified by LLM (iteration 1): ensure m equals one of x or y */
  if x != m && y != m {
    // This case should not occur given our construction
    if x >= y {
      x := m;
      y := s - m;
    } else {
      y := m;
      x := s - m;
    }
  }
}

//IMPL TestMaxSum
method TestMaxSum(x: int, y: int) 
{
}