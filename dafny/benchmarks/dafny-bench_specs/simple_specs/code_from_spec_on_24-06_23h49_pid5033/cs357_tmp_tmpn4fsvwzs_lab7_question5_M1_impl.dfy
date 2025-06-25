//ATOM
method A1(x: int, y: int) returns (r: int)
ensures r == x + y
{
  r := 0;
  /* code modified by LLM (iteration 1): fixed syntax error in assume statement */
  assume r == x + y;
  return r;
}


//IMPL 
method M1(x: int, y: int) returns (r: int)
ensures r == x*y
{
  r := x * y;
}