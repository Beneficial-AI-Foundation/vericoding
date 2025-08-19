method TripleConditions(x: int) returns (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
  /* code modified by LLM (iteration 1): Fixed the implementation to correctly calculate r as 3*x instead of using invalid assume statement */
  r := 3 * x;
  return r;
}


//IMPL 

method Caller() {
}