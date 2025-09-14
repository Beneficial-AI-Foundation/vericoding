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
lemma FibRecurrence(n: nat)
  ensures Fibonacci(n + 2) == Fibonacci(n + 1) + Fibonacci(n)
{
  calc {
    Fibonacci(n + 2);
    == {
      assert n + 2 >= 2;
    }
    Fibonacci((n + 2) - 1) + Fibonacci((n + 2) - 2);
    == {
      assert (n + 2) - 1 == n + 1;
      assert (n + 2) - 2 == n;
    }
    Fibonacci(n + 1) + Fibonacci(n);
  }
}
// </vc-helpers>

// <vc-spec>
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
// </vc-spec>
// <vc-code>
{
  var a: nat := 0;
  var b: nat := 1;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant a == Fibonacci(i)
    invariant b == Fibonacci(i + 1)
    decreases n - i
  {
    var t := a + b;
    FibRecurrence(i);
    assert t == Fibonacci(i + 2);
    a := b;
    b := t;
    i := i + 1;
  }
  return a;
}
// </vc-code>

