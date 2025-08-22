// definition of Fibonacci numbers
// ATOM 
// definition of Fibonacci numbers
function Fibonacci(n: nat): nat {
  match n {
    case 0 => 0
    case 1 => 1
    case _ => Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}

//IMPL iterative calculation of Fibonacci numbers
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
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
      invariant prev == Fibonacci(i - 2)
      invariant curr == Fibonacci(i - 1)
    {
      var next := prev + curr;
      prev := curr;
      curr := next;
      i := i + 1;
    }
    
    f := curr;
  }
}