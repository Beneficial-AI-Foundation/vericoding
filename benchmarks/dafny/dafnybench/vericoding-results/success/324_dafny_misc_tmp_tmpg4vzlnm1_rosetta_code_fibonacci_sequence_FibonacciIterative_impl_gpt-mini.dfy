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
lemma FibSuccSum(k: nat)
  ensures Fibonacci(k+2) == Fibonacci(k+1) + Fibonacci(k)
{
  if k == 0 {
    // Fibonacci(2) == Fibonacci(1) + Fibonacci(0)
    assert Fibonacci(2) == Fibonacci(1) + Fibonacci(0);
  } else {
    // For k >= 1, by the definition of Fibonacci for n >= 2
    assert Fibonacci(k+2) == Fibonacci(k+1) + Fibonacci(k);
  }
}
// </vc-helpers>

// <vc-spec>
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var a := 0;
  var b := 1;
  while i < n
    invariant 0 <= i <= n
    invariant a == Fibonacci(i)
    invariant b == Fibonacci(i+1)
    decreases n - i
  {
    var tmp := a;
    a := b;
    b := tmp + b;
    i := i + 1;
  }
  f := a;
}
// </vc-code>

