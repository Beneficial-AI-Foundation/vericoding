// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
// </vc-spec>
// <vc-code>
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
// </vc-code>

// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0