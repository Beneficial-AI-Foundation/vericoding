// Ex 1.3
//ATOM_PLACEHOLDER_Triple

//ATOM_PLACEHOLDER_Caller

// Ex 1.6
//ATOM_PLACEHOLDER_MinUnderSpec

//ATOM_PLACEHOLDER_Min

// Ex 1.7
//ATOM_PLACEHOLDER_MaxSum//ATOM_PLACEHOLDER_MaxSumCaller

// Ex 1.8
//IMPL ReconstructFromMaxSum
method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
  // requires (0 < s && s / 2 < m && m < s)
  requires s - m <= m
  ensures s == x + y
  ensures (m == y || m == x) && x <= m && y <= m
{
  x := m;
  y := s - m;
}

//ATOM_PLACEHOLDER_TestMaxSum

// Ex 1.9
//ATOM_PLACEHOLDER_Average

//ATOM_PLACEHOLDER_Triple'