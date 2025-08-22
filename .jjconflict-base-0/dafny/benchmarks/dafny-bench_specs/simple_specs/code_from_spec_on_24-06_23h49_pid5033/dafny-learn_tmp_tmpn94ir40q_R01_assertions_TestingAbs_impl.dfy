//ATOM
method Abs(x: int) returns (y: int)
 ensures 0 <= y
 ensures x < 0 ==> y == -x
 ensures x >= 0 ==> y == x
{
  y := 0;
  assume 0 <= y;
  assume x < 0 ==> y == -x;
  assume x >= 0 ==> y == x;
  return y;
}

//IMPL TestingAbs
method TestingAbs()
{
  var result1 := Abs(5);
  var result2 := Abs(-3);
  var result3 := Abs(0);
}