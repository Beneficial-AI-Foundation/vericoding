// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

// <vc-helpers>
lemma FactSucc(m: nat)
  ensures Factorial(m+1) == (m+1) * Factorial(m)
{
  // By definition of Factorial, since m+1 > 0 the else branch applies
  assert Factorial(m+1) == (m+1) * Factorial(m)
}
// </vc-helpers>

// <vc-spec>
method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
// </vc-spec>
// <vc-code>
{
  var res: nat := 1;
  var i: nat := 1;
  while i <= n
    invariant 1 <= i <= n+1
    invariant res == Factorial(i-1)
  {
    var oldi := i;
    res := res * oldi;
    FactSucc(oldi - 1);
    assert res == Factorial(oldi);
    i := oldi + 1;
    assert res == Factorial(i-1);
  }
  u := res;
}
// </vc-code>

