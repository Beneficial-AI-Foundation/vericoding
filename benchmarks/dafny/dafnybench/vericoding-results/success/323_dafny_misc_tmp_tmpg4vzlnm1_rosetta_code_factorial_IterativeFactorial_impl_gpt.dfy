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
  var r: nat := 1;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant r == Factorial(i)
    decreases n - i
  {
    i := i + 1;
    assert i > 0;
    r := i * r;
  }
  result := r;
}
// </vc-code>

