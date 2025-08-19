method Add(x: int, y: int) returns (r: int)
 ensures r == x+y
{
  r := 0;
  /* code modified by LLM (iteration 1): fixed compilation errors - removed invalid assume statement and set r to correct value */
  r := x + y;
  return r;
}


//IMPL SPEC

method Mul(x: int, y: int) returns (r: int)
 ensures r == x*y
{
  r := x * y;
}