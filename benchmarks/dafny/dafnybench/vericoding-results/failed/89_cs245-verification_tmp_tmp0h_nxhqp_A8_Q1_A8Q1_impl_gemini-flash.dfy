// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Dafny.
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= n;
  decreases n;
  {
    if (n == 0) then 1 else a * power(a, n - 1)
  }

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/

// <vc-helpers>
function Multiply(a: int, b: int): int
  ensures Multiply(a,b) == a * b
{
  a * b
}
// </vc-helpers>

// <vc-spec>
method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
ensures z==power(x,y0)
// </vc-spec>
// <vc-code>
{
  var y := y0;
  var r := 1;
  var b := x;

  while y > 0
    invariant y >= 0
    invariant r * power(b, y) == power(x, y0) // Original invariant
  {
    if y % 2 == 1 {
      r := r * b; // Directly use multiplication instead of helper for simplicity and to avoid potential issues with `Multiply` definition scope
      y := y - 1;
    }
    // Optimization: Only update b and y if y is still greater than 0. If y became 0 in the
    // previous if block, we should exit.
    if y > 0 {
      b := b * b; // Directly use multiplication
      y := y / 2;
    }
  }
  z := r;
}
// </vc-code>

