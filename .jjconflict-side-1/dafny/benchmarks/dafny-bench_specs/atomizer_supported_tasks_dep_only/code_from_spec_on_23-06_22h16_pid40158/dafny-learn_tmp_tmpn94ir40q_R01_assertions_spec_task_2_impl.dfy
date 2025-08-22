//IMPL Abs
method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}

//IMPL TestingAbs
method TestingAbs()
{
  var result := Abs(-5);
  assert result == 5;
  
  var result2 := Abs(3);
  assert result2 == 3;
  
  var result3 := Abs(0);
  assert result3 == 0;
}

//IMPL TestingAbs2
/* code modified by LLM (iteration 1): renamed duplicate method from TestingAbs to TestingAbs2 to fix compilation error */
method TestingAbs2()
{
  var val := Abs(-10);
  assert val >= 0;
  assert val == 10;
}