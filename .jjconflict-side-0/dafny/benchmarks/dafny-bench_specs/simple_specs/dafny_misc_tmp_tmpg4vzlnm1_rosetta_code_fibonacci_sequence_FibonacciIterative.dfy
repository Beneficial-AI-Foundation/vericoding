//ATOM
// definition of Fibonacci numbers
function Fibonacci(n: nat): nat {
 match n {
  case 0 => 0
  case 1 => 1
  case _ => Fibonacci(n - 1) + Fibonacci(n - 2)
 }
}


// SPEC

// iterative calculation of Fibonacci numbers
method FibonacciIterative(n: nat) returns (f: nat)
 ensures f == Fibonacci(n)
{
}
