// <vc-preamble>
function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}
// </vc-preamble>

// <vc-helpers>
lemma FibFibRecurrence(n: nat)
  requires n >= 3
  ensures fibfib(n) == fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
{ }
// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)

  ensures result == fibfib(n)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  var a: nat := 0;
  var b: nat := 0;
  var c: nat := 1;
  while i < n
    invariant i <= n
    invariant a == fibfib(i)
    invariant b == fibfib(i + 1)
    invariant c == fibfib(i + 2)
    decreases n - i
  {
    var next: nat := a + b + c;
    FibFibRecurrence(i + 3);
    a, b, c := b, c, next;
    i := i + 1;
  }
  result := a;
}
// </vc-code>
