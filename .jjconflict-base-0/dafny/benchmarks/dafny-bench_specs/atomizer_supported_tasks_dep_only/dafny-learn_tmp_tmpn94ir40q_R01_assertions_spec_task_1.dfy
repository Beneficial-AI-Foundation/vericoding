// SPEC 
method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
{
}


//ATOM_PLACEHOLDER_TestingAbs

//ATOM_PLACEHOLDER_TestingAbs2



// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
//ATOM_PLACEHOLDER_Max
//ATOM_PLACEHOLDER_TestingMax

