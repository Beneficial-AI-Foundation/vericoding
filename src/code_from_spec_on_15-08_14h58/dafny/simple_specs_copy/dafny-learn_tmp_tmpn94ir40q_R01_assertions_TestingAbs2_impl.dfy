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
  /* code modified by LLM (iteration 1): Added explicit variable declarations and assertions based on the postconditions of Abs method */
  var result1 := Abs(5);
  assert result1 >= 0; // from ensures 0 <= y
  assert 5 >= 0 ==> result1 == 5; // from ensures x >= 0 ==> y == x
  assert result1 == 5;
  
  var result2 := Abs(-3);
  assert result2 >= 0; // from ensures 0 <= y  
  assert -3 < 0 ==> result2 == -(-3); // from ensures x < 0 ==> y == -x
  assert result2 == 3;
  
  var result3 := Abs(0);
  assert result3 >= 0; // from ensures 0 <= y
  assert 0 >= 0 ==> result3 == 0; // from ensures x >= 0 ==> y == x
  assert result3 == 0;
}