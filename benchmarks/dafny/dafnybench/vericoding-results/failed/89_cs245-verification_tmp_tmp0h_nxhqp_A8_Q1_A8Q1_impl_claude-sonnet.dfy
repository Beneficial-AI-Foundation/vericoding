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
lemma PowerAdditive(a: int, m: int, n: int)
  requires m >= 0 && n >= 0
  ensures power(a, m + n) == power(a, m) * power(a, n)
  decreases m
{
  if m == 0 {
    assert power(a, 0 + n) == power(a, n);
    assert power(a, 0) * power(a, n) == 1 * power(a, n) == power(a, n);
  } else {
    PowerAdditive(a, m - 1, n);
    assert power(a, m + n) == power(a, (m - 1) + 1 + n) == power(a, (m - 1) + (1 + n));
    assert power(a, (m - 1) + (1 + n)) == power(a, m - 1) * power(a, 1 + n);
    assert power(a, 1 + n) == a * power(a, n);
    assert power(a, m - 1) * power(a, 1 + n) == power(a, m - 1) * a * power(a, n);
    assert power(a, m) == a * power(a, m - 1);
    assert power(a, m) * power(a, n) == a * power(a, m - 1) * power(a, n);
  }
}

lemma PowerStep(a: int, n: int)
  requires n >= 0
  ensures a * power(a, n) == power(a, n + 1)
{
  assert power(a, n + 1) == a * power(a, n);
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
  z := 1;
  
  while y > 0
    invariant y >= 0
    invariant z * power(x, y) == power(x, y0)
    decreases y
  {
    PowerStep(x, y - 1);
    z := z * x;
    y := y - 1;
  }
}
// </vc-code>

