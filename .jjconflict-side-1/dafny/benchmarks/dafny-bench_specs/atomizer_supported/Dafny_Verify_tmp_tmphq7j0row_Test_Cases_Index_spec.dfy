// SPEC 
method Index(n: int) returns (i: int) 
requires 1 <= n
ensures 0 <= i < n
{
}


// SPEC 

method Min(x: int, y: int) returns (m: int) 
ensures m <= x && m <= y
ensures m == x || m == y
{
}


// SPEC 

method Max(x: int, y: int) returns (m: int) {
}



// SPEC 


method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
}



// SPEC 


method MaxSumCaller() {
}


// SPEC 

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s <= 2 * m
    ensures s == (x + y)
    ensures (m == x || m == y) && x <= m && y <= m
{
}



// SPEC 


method TestMaxSum(x: int, y: int) 
{
}




