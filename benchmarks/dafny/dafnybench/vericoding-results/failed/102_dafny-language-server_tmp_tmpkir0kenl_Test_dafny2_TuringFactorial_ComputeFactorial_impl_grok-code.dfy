// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

// <vc-helpers>
// Proof for Factorial computation correctness
// Note: The original implementation is correct, but we can add invariants or lemmas if needed.
// Since the loop invariant holds and the logic is sound for 1 <= n, no additional helpers are required.
// </vc-helpers>

// <vc-spec>
method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
// </vc-spec>
// <vc-code>
{
  u := 1;
  var i := 1;
  while i < n
    decreases n - i
    invariant 1 <= i <= n
    invariant u == Factorial(i)
  {
    i := i + 1;
    u := u * i;
  }
}
// </vc-code>

