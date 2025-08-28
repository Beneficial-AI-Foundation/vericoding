// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

// <vc-helpers>
lemma FactorialPositive(n: nat)
  ensures Factorial(n) > 0
{
  if n == 0 {
  } else {
    FactorialPositive(n-1);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  u := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant u == Factorial(i - 1)
  {
    u := u * i;
    i := i + 1;
  }
}
// </vc-code>
