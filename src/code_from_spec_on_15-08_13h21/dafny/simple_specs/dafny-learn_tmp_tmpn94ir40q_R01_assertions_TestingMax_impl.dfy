//ATOM

// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
method Max(a: int, b: int) returns (c: int)
 ensures c >= a
 ensures c >= b
{
  c := 0;
  assume c >= a;
  assume c >= b;
  return c;
}

//IMPL
method TestingMax() {
  /* code modified by LLM (iteration 1): Added proper test implementation that calls Max method and asserts properties based on the method's ensures clauses */
  var result := Max(5, 3);
  assert result >= 5;
  assert result >= 3;
  
  // Additional test with different values to make the test more comprehensive
  var result2 := Max(10, 15);
  assert result2 >= 10;
  assert result2 >= 15;
}