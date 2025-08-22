//ATOM Abs
function Abs(x: int): int
{
  if x < 0 then -x else x
}

//ATOM TestingAbs
method TestingAbs()
{
  assert Abs(3) == 3;
  assert Abs(-3) == 3;
  assert Abs(0) == 0;
}

//ATOM TestingAbs2
method TestingAbs2()
{
  assert Abs(-5) == 5;
  assert Abs(10) == 10;
}

//IMPL Max
method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
{
  /* code modified by LLM (iteration 1): Fixed implementation to properly satisfy postconditions */
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}

//ATOM TestingMax
/* code modified by LLM (iteration 1): Fixed method name from TestingAbs to TestingMax to avoid duplicate names */
method TestingMax()
{
  var result := Max(5, 3);
  assert result >= 5;
  assert result >= 3;
  assert result == 5;
}