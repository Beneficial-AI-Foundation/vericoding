// Ex 1.3
//ATOM_PLACEHOLDER_Triple

//ATOM_PLACEHOLDER_Caller

// Ex 1.6
//ATOM_PLACEHOLDER_MinUnderSpec

//ATOM_PLACEHOLDER_Min

// Ex 1.7
// SPEC 

// Ex 1.7
method MaxSum (x: int, y: int) returns (s:int, m: int)
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y
// SPEC 

// Ex 1.7
method MaxSum (x: int, y: int) returns (s:int, m: int)
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y
Caller

// Ex 1.8
// SPEC 

// Ex 1.8
method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
  // requires (0 < s && s / 2 < m && m < s)
  requires s - m <= m
  ensures s == x + y
  ensures (m == y || m == x) && x <= m && y <= m
{
}


// SPEC 

method TestMaxSum(x: int, y: int)
  // requires x > 0 && y > 0 && x != y
{
}


// Ex 1.9
//ATOM_PLACEHOLDER_Average

//ATOM_PLACEHOLDER_Triple'

