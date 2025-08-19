//ATOM
method MaxSum(x: int, y: int) returns (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  /* code modified by LLM (iteration 1): Fixed assignment statements to properly assign values instead of using incorrect implication operator */
  s := x + y;
  m := if x >= y then x else y;
}

//IMPL 

method MaxSumCaller() {
  var sum, max := MaxSum(5, 3);
}