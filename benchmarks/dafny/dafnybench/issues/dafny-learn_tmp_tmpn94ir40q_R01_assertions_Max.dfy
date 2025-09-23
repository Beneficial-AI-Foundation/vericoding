// <vc-preamble>
// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
// </vc-spec>
// <vc-code>
{
  c := a;
  if b > c {
    c := b;
  }
}
// </vc-code>
