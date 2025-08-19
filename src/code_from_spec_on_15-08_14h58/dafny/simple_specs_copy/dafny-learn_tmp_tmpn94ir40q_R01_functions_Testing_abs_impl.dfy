//ATOM
function abs(x: int): int
{
  if x < 0 then -x else x
}

//IMPL Testing_abs
method Testing_abs()
{
    // Test positive numbers
    assert abs(5) == 5;
    assert abs(10) == 10;
    
    // Test negative numbers
    assert abs(-5) == 5;
    assert abs(-10) == 10;
    
    // Test zero
    assert abs(0) == 0;
}