/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of a real number (x^n), 
* illustrating the usage of lemmas and automatic induction in Dafny.
* J.  Pascoal Faria, FEUP, Jan/2022.
*/

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Computation of x^n in time and space O(log n).

// <vc-helpers>
lemma powerEven(x: real, n: nat)
  requires n % 2 == 0
  ensures power(x, n) == power(x * x, n / 2)
{
  if n == 0 {
    // Base case: power(x, 0) == 1.0 == power(x * x, 0)
  } else {
    // Inductive case
    var m := n / 2;
    assert n == 2 * m;
    powerDouble(x, m);
  }
}

lemma powerDouble(x: real, n: nat)
  ensures power(x, 2 * n) == power(x * x, n)
{
  if n == 0 {
    // Base case: power(x, 0) == 1.0
  } else {
    // Inductive case
    calc == {
      power(x, 2 * n);
      x * power(x, 2 * n - 1);
      x * x * power(x, 2 * n - 2);
      x * x * power(x, 2 * (n - 1));
      { powerDouble(x, n - 1); }
      x * x * power(x * x, n - 1);
      power(x * x, n);
    }
  }
}

lemma powerOdd(x: real, n: nat)
  requires n % 2 == 1
  ensures power(x, n) == x * power(x * x, n / 2)
{
  if n == 1 {
    // Base case: power(x, 1) == x == x * power(x * x, 0)
    assert power(x, 1) == x;
    assert power(x * x, 0) == 1.0;
  } else {
    // n is odd and n > 1, so n = 2 * m + 1 for some m >= 1
    var m := n / 2;
    assert n == 2 * m + 1;
    calc == {
      power(x, n);
      power(x, 2 * m + 1);
      x * power(x, 2 * m);
      { powerDouble(x, m); }
      x * power(x * x, m);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
decreases n
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    var q := powerDC(x * x, n / 2);
    powerEven(x, n);
    p := q;
  } else {
    var q := powerDC(x * x, n / 2);
    powerOdd(x, n);
    p := x * q;
  }
}
// </vc-code>

// A few test cases (checked statically by Dafny).