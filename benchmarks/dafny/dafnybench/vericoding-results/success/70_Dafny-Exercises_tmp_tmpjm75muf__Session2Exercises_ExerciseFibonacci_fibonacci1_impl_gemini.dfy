// <vc-preamble>
function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}
// </vc-preamble>

// <vc-helpers>
lemma FibProperty(k: nat)
  requires k >= 1
  ensures fib(k+1) == fib(k) + fib(k-1)
{
}
// </vc-helpers>

// <vc-spec>
method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    f := 0;
  } else {
    var a: nat := 0;
    var b: nat := 1;
    var i := 1;
    while i < n
      invariant 1 <= i <= n
      invariant a == fib(i - 1)
      invariant b == fib(i)
      decreases n - i
    {
      a, b := b, a + b;
      i := i + 1;
    }
    f := b;
  }
}
// </vc-code>
