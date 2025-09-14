// <vc-preamble>
function Fibonacci(n: nat): nat {
  match n {
    case 0 => 0
    case 1 => 1
    case _ => Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}
// </vc-preamble>

// <vc-helpers>
predicate IsFibPair(i: nat, a: nat, b: nat)
{
  a == Fibonacci(i) && b == Fibonacci(i+1)
}
// </vc-helpers>

// <vc-spec>
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  var a: nat := 0;
  var b: nat := 1;
  while i < n
    invariant i <= n
    invariant IsFibPair(i, a, b)
  {
    a, b := b, a + b;
    i := i + 1;
  }
  f := a;
}
// </vc-code>
