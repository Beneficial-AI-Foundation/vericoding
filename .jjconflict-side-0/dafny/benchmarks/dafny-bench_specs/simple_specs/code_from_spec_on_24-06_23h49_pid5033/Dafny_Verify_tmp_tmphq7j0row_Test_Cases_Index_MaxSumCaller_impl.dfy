//ATOM
method MaxSum(x: int, y: int) returns (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  /* code modified by LLM (iteration 1): Fixed assume statements to use correct assignment syntax */
  s := x + y;
  m := if x >= y then x else y;
  return s, m;
}

//IMPL MaxSumCaller
method MaxSumCaller() {
  /* code modified by LLM (iteration 1): No changes needed - this implementation is correct */
  var sum, max := MaxSum(5, 3);
}