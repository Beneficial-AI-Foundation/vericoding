//IMPL 
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


//ATOM_PLACEHOLDER_TestingAbs

//IMPL 
method TestingAbs2()
{
  var result := Abs(-5);
  assert result == 5;
  
  var result2 := Abs(3);
  assert result2 == 3;
  
  var result3 := Abs(0);
  assert result3 == 0;
}




// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
//ATOM_PLACEHOLDER_Max
//ATOM_PLACEHOLDER_TestingMax