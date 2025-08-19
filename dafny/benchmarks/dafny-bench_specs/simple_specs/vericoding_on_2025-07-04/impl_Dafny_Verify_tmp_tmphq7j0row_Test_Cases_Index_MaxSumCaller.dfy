//ATOM
method MaxSum(x: int, y: int) returns (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  /* code modified by LLM (iteration 1): fixed assignment and assume statements to satisfy postconditions */
  s := x + y;
  m := if x >= y then x else y;
  return s, m;
}

// SPEC
method MaxSumCaller() {
}