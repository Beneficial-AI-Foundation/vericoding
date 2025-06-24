//ATOM_PLACEHOLDER_Abs

//ATOM_PLACEHOLDER_TestingAbs

//ATOM_PLACEHOLDER_TestingAbs2

// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
//IMPL Max
method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
{
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}

// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
//IMPL TestingMax
method TestingMax() {
  var result := Max(5, 3);
  assert result >= 5;
  assert result >= 3;
  
  var result2 := Max(-1, -5);
  assert result2 >= -1;
  assert result2 >= -5;
}