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
set-options "--allow-warnings"
// </vc-helpers>

// <vc-spec>
method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
ensures z==power(x,y0)
// </vc-spec>
// <vc-code>
{
  z := 1;
  var y := 0;
  while y < y0
    invariant 0 <= y && y <= y0
    invariant z == power(x, y)
    decreases y0 - y
  {
    var oy := y;
    var oz := z;

    y := oy + 1;
    z := x * oz;

    assert oz == power(x, oy);
    assert power(x, oy + 1) == x * power(x, oy);
    assert z == power(x, y);
  }
}
// </vc-code>

