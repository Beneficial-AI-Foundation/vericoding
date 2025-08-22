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

//ATOM_PLACEHOLDER_ReconstructFromMaxSum

//ATOM_PLACEHOLDER_TestMaxSum