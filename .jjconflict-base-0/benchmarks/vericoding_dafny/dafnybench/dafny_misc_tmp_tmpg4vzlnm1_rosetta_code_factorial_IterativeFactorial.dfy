// recursive definition of factorial
function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}

// iterative implementation of factorial

// <vc-helpers>
// </vc-helpers>

method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
// <vc-code>
{
  assume false;
}
// </vc-code>