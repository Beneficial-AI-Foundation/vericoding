function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}

// iterative implementation of factorial

// <vc-helpers>
// </vc-helpers>

method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
// </vc-spec>
// <vc-code>
{
  result := 1;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant result == Factorial(i)
  {
    i := i + 1;
    result := result * i;
  }
}
// </vc-code>