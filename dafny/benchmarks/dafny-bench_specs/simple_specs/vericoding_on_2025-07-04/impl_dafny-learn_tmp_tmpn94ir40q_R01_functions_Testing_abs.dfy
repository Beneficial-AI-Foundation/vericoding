//ATOM
function abs(x: int): int
{
  if x < 0 then -x else x
}

//IMPL 
method Testing_abs()
{
  // Test positive number
  var result1 := abs(5);
  assert result1 == 5;
  
  // Test negative number
  var result2 := abs(-3);
  assert result2 == 3;
  
  // Test zero
  var result3 := abs(0);
  assert result3 == 0;
}