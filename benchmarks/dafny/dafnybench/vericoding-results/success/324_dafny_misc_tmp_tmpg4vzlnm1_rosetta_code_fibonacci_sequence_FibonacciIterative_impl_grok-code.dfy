// definition of Fibonacci numbers
function Fibonacci(n: nat): nat {
  match n {
    case 0 => 0
    case 1 => 1
    case _ => Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}

// iterative calculation of Fibonacci numbers

// <vc-helpers>
// No updates needed in helpers
// </vc-helpers>

// <vc-spec>
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    f := 0;
  } else if n == 1 {
    f := 1;
  } else {
    var prev := 0;
    var curr := 1;
    var i := 2;
    while i <= n
      invariant 2 <= i <= n + 1
      invariant curr == Fibonacci(i - 1)
      invariant prev == Fibonacci(i - 2)
    {
      var next := prev + curr;
      prev := curr;
      curr := next;
      i := i + 1;
    }
    f := curr;
  }
}
// </vc-code>

