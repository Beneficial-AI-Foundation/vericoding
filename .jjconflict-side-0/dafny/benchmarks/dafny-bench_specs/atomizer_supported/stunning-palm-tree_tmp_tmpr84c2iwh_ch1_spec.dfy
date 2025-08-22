// Ex 1.3
// SPEC 

method Triple'(x: int) returns (r: int)
  // spec 1: ensures Average(r, 3*x) == 3*x
  ensures Average(2*r, 6*x) == 6*x
{
}


// SPEC 

method Caller() {
}


// Ex 1.6
// SPEC 

// Ex 1.6
method MinUnderSpec (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y {
}


// SPEC 

method Min (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y {
}


// Ex 1.7
// SPEC 

// Ex 1.7
method MaxSum (x: int, y: int) returns (s:int, m: int)
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y
// SPEC 
// look ma, no implementation!

method MaxSumCaller() {
}


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
// ATOM 

// Ex 1.9
function Average (a: int, b: int): int {
  (a + b) / 2
}




