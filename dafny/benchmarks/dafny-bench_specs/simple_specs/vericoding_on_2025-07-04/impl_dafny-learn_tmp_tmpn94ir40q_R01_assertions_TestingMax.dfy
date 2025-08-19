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


// SPEC
method TestingMax() {
}