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
lemma PowerAdditive(x: real, a: nat, b: nat)
  ensures power(x, a+b) == power(x, a) * power(x, b)
{
  if b == 0 {
  } else {
    PowerAdditive(x, a, b-1);
    assert power(x, a+b) == x * power(x, a+b-1);
    assert power(x, a+b-1) == power(x, a) * power(x, b-1);
    assert power(x, a+b) == x * (power(x, a) * power(x, b-1));
    assert power(x, a+b) == power(x, a) * (x * power(x, b-1));
    assert power(x, a+b) == power(x, a) * power(x, b);
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
    return 1.0;
  } else {
    var k := n / 2;
    var half := powerDC(x, k);
    var halfsq := half * half;
    if n % 2 == 0 {
      assert 2 * k == n;
      PowerAdditive(x, k, k);
      return halfsq;
    } else {
      assert 2 * k + 1 == n;
      PowerAdditive(x, k, k);
      PowerAdditive(x, 1, 2*k);
      return x * halfsq;
    }
  }
}
// </vc-code>

// A few test cases (checked statically by Dafny).