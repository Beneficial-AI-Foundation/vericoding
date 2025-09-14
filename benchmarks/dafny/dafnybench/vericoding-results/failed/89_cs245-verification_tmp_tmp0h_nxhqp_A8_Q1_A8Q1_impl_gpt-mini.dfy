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
// No helpers needed; 'power' is defined in the preamble.
// </vc-helpers>

// <vc-spec>
method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
ensures z==power(x,y0)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  z := 1;
  while i < y0
    invariant 0 <= i <= y0
    invariant z == power(x, i)
    decreases y0 - i
  {
    z := z * x;
    i := i + 1;
  }
}
// </vc-code>

