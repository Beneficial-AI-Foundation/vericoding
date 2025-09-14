// recursive definition of factorial
function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}

// iterative implementation of factorial

// <vc-helpers>
// Helper lemma to allow unfolding of Factorial when n > 0
lemma FactorialUnfold(n: nat)
  ensures n > 0 ==> Factorial(n) == n * Factorial(n - 1)
{
  if n == 0 {
  } else {
    // By definition of the recursive function Factorial
    assert Factorial(n) == n * Factorial(n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
// </vc-spec>
// <vc-code>
{
  result := 1;
  var i: nat := n;
  while i > 0
    invariant result * Factorial(i) == Factorial(n)
    invariant i <= n
    decreases i
  {
    // ensure i-1 is in nat when unfolding Factorial
    assert i > 0;
    assert Factorial(i) == i * Factorial(i - 1);
    result := result * i;
    i := i - 1;
  }
  // At loop exit i == 0, use the invariant to conclude the postcondition
  assert i == 0;
  assert result * Factorial(i) == Factorial(n);
  assert Factorial(i) == 1;
  assert result == Factorial(n);
}
// </vc-code>

