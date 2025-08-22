//ATOM_PLACEHOLDER_Index

//ATOM_PLACEHOLDER_Min

//ATOM_PLACEHOLDER_Max


//IMPL MaxSum
method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
  s := x + y;
  m := if x >= y then x else y;
}


//IMPL MaxSumCaller
method MaxSumCaller() {
}


//ATOM_PLACEHOLDER_ReconstructFromMaxSum


//ATOM_PLACEHOLDER_TestMaxSum