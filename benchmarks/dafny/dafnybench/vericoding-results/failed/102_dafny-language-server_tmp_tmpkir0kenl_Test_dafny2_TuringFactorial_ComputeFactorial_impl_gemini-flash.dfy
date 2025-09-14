// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

// <vc-helpers>
lemma Factorial_property(k: nat)
  ensures Factorial(k) > 0
{
  if k > 0 {
    Factorial_property(k-1);
  }
}

lemma Factorial_times_n(n: nat, i: nat)
  requires 1 <= i <= n
  ensures Factorial(i-1) * i == Factorial(i)
{}
// </vc-helpers>

// <vc-spec>
method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
// </vc-spec>
// <vc-code>
{
  var u_local: int := 1;
  var i: int := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant u_local == Factorial(i - 1)
    invariant u_local > 0
  {
    u_local := u_local * i;
    i := i + 1;
  }
  return u_local;
}
// </vc-code>

