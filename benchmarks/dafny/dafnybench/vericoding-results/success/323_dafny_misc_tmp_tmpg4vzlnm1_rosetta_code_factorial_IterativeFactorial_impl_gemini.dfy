// <vc-preamble>
function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
// </vc-spec>
// <vc-code>
{
  result := 1;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result == Factorial(i)
    decreases n - i
  {
    i := i + 1;
    result := result * i;
  }
}
// </vc-code>
