// recursive definition of factorial
function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}

// iterative implementation of factorial

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
// </vc-spec>
// <vc-code>
{
  var res: nat := 1;
  var i: nat := 1;
  while i <= n
    invariant 1 <= i <= n + 1 && res == Factorial(i - 1)
  {
    res := res * i;
    i := i + 1;
  }
  result := res;
}
// </vc-code>

