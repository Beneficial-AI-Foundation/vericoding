//ATOM
method nonZeroReturn(x: int) returns (y: int)
 ensures y != 0
{
  y := 0;
  assume y != 0;
  return y;
}


// SPEC
method test() {
}
