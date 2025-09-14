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
lemma PowerLemma(a: int, n: int, m: int)
  requires 0 <= n && 0 <= m
  ensures power(a, n + m) == power(a, n) * power(a, m)
  decreases n
{
  if n == 0 {
    assert power(a, 0 + m) == power(a, m);
    assert power(a, 0) * power(a, m) == 1 * power(a, m) == power(a, m);
  } else {
    PowerLemma(a, n - 1, m);
    calc {
      power(a, n + m);
      a * power(a, n + m - 1);
      a * (power(a, n - 1) * power(a, m));
      (a * power(a, n - 1)) * power(a, m);
      power(a, n) * power(a, m);
    }
  }
}

lemma PowerSquareLemma(a: int, n: int)
  requires 0 <= n
  ensures power(a, 2 * n) == power(a, n) * power(a, n)
  decreases n
{
  if n == 0 {
    // Trivial case
  } else {
    PowerSquareLemma(a, n - 1);
    PowerLemma(a, n, n);
    assert power(a, 2 * n) == power(a, n + n) == power(a, n) * power(a, n);
  }
}

lemma EvenPowerLemma(a: int, n: int)
  requires 0 <= n && n % 2 == 0
  ensures power(a, n) == power(a * a, n / 2)
  decreases n
{
  if n > 0 {
    calc {
      power(a, n);
      power(a, n/2 + n/2);
      { PowerLemma(a, n/2, n/2); }
      power(a, n/2) * power(a, n/2);
      { PowerMultiplicationLemma(a, a, n/2); }
      power(a * a, n / 2);
    }
  } else {
    assert n == 0;
  }
}

lemma PowerMultiplicationLemma(a: int, b: int, n: int)
  requires 0 <= n
  ensures power(a, n) * power(b, n) == power(a * b, n)
  decreases n
{
  if n == 0 {
    assert power(a, 0) * power(b, 0) == 1 * 1 == 1;
    assert power(a * b, 0) == 1;
  } else {
    PowerMultiplicationLemma(a, b, n - 1);
    calc {
      power(a, n) * power(b, n);
      a * power(a, n-1) * b * power(b, n-1);
      a * b * (power(a, n-1) * power(b, n-1));
      a * b * power(a * b, n-1);
      power(a * b, n);
    }
  }
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
  var x_var := x;
  z := 1;
  
  while (y > 0)
    invariant y >= 0
    invariant z * power(x_var, y) == power(x, y0)
  {
    if (y % 2 == 1) {
      z := z * x_var;
      y := y - 1;
    } else {
      EvenPowerLemma(x_var, y);
      x_var := x_var * x_var;
      y := y / 2;
    }
  }
}
// </vc-code>

