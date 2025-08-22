//IMPL nonZeroReturn
method nonZeroReturn(x: int) returns (y: int)
  ensures y != 0
{
  y := 1;
}

//IMPL test
method test() {
}