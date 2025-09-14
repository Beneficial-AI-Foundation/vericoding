// <vc-preamble>
function fib(n: nat): nat
  decreases n;
{
  if n == 0 then 0 
  else if n == 1 then 1 
  else fib(n - 1) + fib(n - 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added a lemma to state the fibonacci property to help the verifier. */
lemma FibDefinition(k: nat)
  requires k >= 2
  ensures fib(k) == fib(k-1) + fib(k-2)
{
}
// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Added a call to FibDefinition lemma to aid verification. */
  if n <= 1 {
    f := n;
  } else {
    var a: nat := 0;
    var b: nat := 1;
    var i: nat := 2;
    while i <= n
      invariant i >= 2 && i <= n + 1
      invariant a == fib(i - 2)
      invariant b == fib(i - 1)
      decreases n - i
    {
      FibDefinition(i);
      a, b := b, a + b;
      i := i + 1;
    }
    f := b;
  }
}
// </vc-code>
