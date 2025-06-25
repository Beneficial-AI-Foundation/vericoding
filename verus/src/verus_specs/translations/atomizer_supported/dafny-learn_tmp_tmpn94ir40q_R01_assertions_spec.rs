// SPEC 
pub fn Abs(x: int) -> (y: int)
    ensures(0 <= y)
    ensures(x < 0 ==> y == -x)
    ensures(x >= 0 ==> y == x)
{
}

// SPEC 
pub fn TestingAbs()
{
}

// SPEC 
pub fn TestingAbs2()
{
}

// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
// SPEC 

// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
pub fn Max(a: int, b: int) -> (c: int)
    ensures(c >= a)
    ensures(c >= b)
{
}

// SPEC 
pub fn TestingMax() {
}