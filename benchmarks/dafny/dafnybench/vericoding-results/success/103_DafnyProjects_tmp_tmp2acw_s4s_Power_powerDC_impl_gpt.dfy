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
lemma powerSucc(x: real, m: nat)
  ensures power(x, m + 1) == x * power(x, m)
{
}

lemma powerAdd(x: real, a: nat, b: nat)
  ensures power(x, a + b) == power(x, a) * power(x, b)
  decreases a
{
  if a == 0 {
  } else {
    powerAdd(x, a - 1, b);
    powerSucc(x, (a - 1) + b);
    powerSucc(x, a - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    var k: nat := n / 2;
    assert k < n;
    var t := powerDC(x, k);
    p := t * t;
    powerAdd(x, k, k);
    assert p == power(x, k) * power(x, k);
    assert k + k == 2 * k;
    assert n == 2 * k;
    assert power(x, n) == power(x, k + k);
    assert p == power(x, n);
  } else {
    var k: nat := n / 2;
    assert k < n;
    var t := powerDC(x, k);
    p := x * t * t;
    powerSucc(x, k);
    powerAdd(x, k, k + 1);
    assert p == power(x, k) * power(x, k + 1);
    assert n == 2 * k + 1;
    assert k + (k + 1) == 2 * k + 1;
    assert power(x, n) == power(x, k + (k + 1));
    assert p == power(x, n);
  }
}
// </vc-code>

// A few test cases (checked statically by Dafny).