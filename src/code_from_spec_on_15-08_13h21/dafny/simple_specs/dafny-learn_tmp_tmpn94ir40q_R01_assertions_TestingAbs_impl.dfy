//ATOM
method Abs(x: int) returns (y: int)
 ensures 0 <= y
 ensures x < 0 ==> y == -x
 ensures x >= 0 ==> y == x
{
  /* code modified by LLM (iteration 1): implemented proper absolute value logic instead of using assume statements */
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}

//IMPL 
method TestingAbs()
{
  /* code modified by LLM (iteration 1): added proper variable declarations and method calls */
  var result1 := Abs(5);
  var result2 := Abs(-3);
  var result3 := Abs(0);
}