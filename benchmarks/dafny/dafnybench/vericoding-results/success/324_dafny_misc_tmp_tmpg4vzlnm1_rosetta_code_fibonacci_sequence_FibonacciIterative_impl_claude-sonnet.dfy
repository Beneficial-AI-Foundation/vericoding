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
lemma FibonacciIterativeCorreness(n: nat, a: nat, b: nat, i: nat)
  requires i <= n
  requires a == Fibonacci(i)
  requires b == Fibonacci(i + 1)
  ensures Fibonacci(n) == FibonacciIterativeHelper(n, a, b, i)
  decreases n - i
{
  if i == n {
    assert FibonacciIterativeHelper(n, a, b, i) == a;
    assert a == Fibonacci(i);
    assert i == n;
  } else {
    FibonacciIterativeCorreness(n, b, a + b, i + 1);
  }
}

function FibonacciIterativeHelper(n: nat, a: nat, b: nat, i: nat): nat
  requires i <= n
  decreases n - i
{
  if i == n then a
  else FibonacciIterativeHelper(n, b, a + b, i + 1)
}
// </vc-helpers>

// <vc-spec>
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 0;
  } else if n == 1 {
    return 1;
  } else {
    var a := 0;
    var b := 1;
    var i := 0;
    
    while i < n
      invariant i <= n
      invariant a == Fibonacci(i)
      invariant b == Fibonacci(i + 1)
      decreases n - i
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    
    FibonacciIterativeCorreness(n, a, b, i);
    return a;
  }
}
// </vc-code>

