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
lemma FibonacciLemma(n: nat, a: nat, b: nat)
  requires n >= 1
  requires a == Fibonacci(n - 1)
  requires b == Fibonacci(n)
  ensures b + a == Fibonacci(n + 1)
{
  if n == 1 {
    assert Fibonacci(2) == Fibonacci(1) + Fibonacci(0);
    assert Fibonacci(2) == 1 + 0;
    assert b + a == 1 + 0;
  } else {
    assert Fibonacci(n + 1) == Fibonacci(n) + Fibonacci(n - 1);
  }
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
  }
  if n == 1 {
    return 1;
  }
  
  var i := 1;
  var a := 0;  // Fibonacci(i - 1)
  var b := 1;  // Fibonacci(i)
  
  while i < n
    invariant 1 <= i <= n
    invariant a == Fibonacci(i - 1)
    invariant b == Fibonacci(i)
  {
    FibonacciLemma(i, a, b);
    var temp := b;
    b := a + b;
    a := temp;
    i := i + 1;
  }
  
  return b;
}
// </vc-code>

