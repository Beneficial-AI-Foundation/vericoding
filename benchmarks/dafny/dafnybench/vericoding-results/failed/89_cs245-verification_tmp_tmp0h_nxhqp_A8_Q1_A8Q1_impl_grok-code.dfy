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
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= n
  decreases n
  {
    if (n == 0) then 1 else a * power(a, n - 1)
  }
// </vc-helpers>

// <vc-spec>
method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
ensures z==power(x,y0)
// </vc-spec>
// <vc-code>
{
  z := 1;
  var y := y0;
  while y != 0
    invariant 0 <= y <= y0 && z * power(x, y) == power(x, y0)
  {
    z := z * x;
    y := y - 1;
  }
}
// </vc-code>

