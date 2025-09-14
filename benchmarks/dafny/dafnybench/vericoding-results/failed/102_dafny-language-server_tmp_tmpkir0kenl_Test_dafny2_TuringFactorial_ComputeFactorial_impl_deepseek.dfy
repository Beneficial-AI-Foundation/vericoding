// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

// <vc-helpers>
lemma FactorialLemma(n: nat, k: nat, acc: nat)
  requires 0 <= k <= n
  ensures acc * Factorial(n - k) == Factorial(n)
  decreases n - k
{
  if k < n {
    calc {
      acc * Factorial(n - k);
      ==
      acc * ((n - k) * Factorial(n - k - 1));
      == { assert n - k - 1 == n - (k + 1); }
      (acc * (n - k)) * Factorial(n - (k + 1));
    }
    FactorialLemma(n, k+1, acc*(n - k));
  } else {
    assert k == n;
    assert n - k == 0;
    assert Factorial(0) == 1;
  }
}
// </vc-helpers>

// <vc-spec>
method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  var acc: nat := 1;
  while i < n
    invariant 0 <= i <= n
    invariant acc == Factorial(i)
  {
    i := i + 1;
    acc := acc * i;
  }
  assert i == n;
  FactorialLemma(n, i, acc);
  u := acc;
}
// </vc-code>

