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

//IMPL 
method TestingAbs2()
{
  /* code modified by LLM (iteration 1): Added proper implementation with assertions to test the Abs method */
  var result1 := Abs(5);
  assert result1 == 5;
  
  var result2 := Abs(-3);
  assert result2 == 3;
  
  var result3 := Abs(0);
  assert result3 == 0;
}