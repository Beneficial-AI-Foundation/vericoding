// <vc-preamble>
function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
// </vc-preamble>

// <vc-helpers>
lemma FibStep(n: nat) ensures fib(n + 2) == fib(n + 1) + fib(n) { }
// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (result: nat)

  ensures result == fib(n)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  var a: nat := 0;
  var b: nat := 1;
  while i < n
    invariant i <= n
    invariant a == fib(i)
    invariant b == fib(i + 1)
    decreases n - i
  {
    var nextA: nat := b;
    var nextB: nat := b + a;
    FibStep(i);
    assert nextB == fib(i + 2);
    i := i + 1;
    a := nextA;
    b := nextB;
  }
  result := a;
}
// </vc-code>
