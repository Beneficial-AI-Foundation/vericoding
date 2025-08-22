//ATOM_PLACEHOLDER_Index

//ATOM_PLACEHOLDER_Min

//ATOM_PLACEHOLDER_Max


// SPEC 


method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
}



// SPEC 


method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
}
Caller

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




