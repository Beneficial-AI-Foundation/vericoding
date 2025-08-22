//ATOM
function abs(x: int): int
{
  if x < 0 then -x else x
}

//IMPL Testing_abs
method Testing_abs()
{
  // Test the abs function with various values
  var result1 := abs(5);
  var result2 := abs(-3);
  var result3 := abs(0);
  
  // These assertions help verify the abs function works correctly
  assert result1 == 5;
  assert result2 == 3;
  assert result3 == 0;
}