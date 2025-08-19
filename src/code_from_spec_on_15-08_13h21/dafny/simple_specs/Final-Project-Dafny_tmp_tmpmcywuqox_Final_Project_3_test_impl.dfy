method nonZeroReturn(x: int) returns (y: int)
ensures y != 0
{
  /* code modified by LLM (iteration 3): Changed implementation to return non-zero value instead of using assume */
  y := 1;
  return y;
}

//IMPL test
method test() {
  /* code modified by LLM (iteration 2): Added empty method body to make it a valid implementation */
}