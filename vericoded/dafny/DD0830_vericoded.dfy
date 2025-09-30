// recursive definition of factorial
function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}

// iterative implementation of factorial

// <vc-helpers>
lemma FactorialNonZero(n: nat)
  ensures Factorial(n) != 0
{
  if n == 0 {
    assert Factorial(0) == 1;
  } else {
    FactorialNonZero(n - 1);
    assert Factorial(n) == n * Factorial(n - 1);
    assert n > 0;
    assert Factorial(n - 1) != 0;
  }
}

lemma FactorialDivideItself(n: nat)
  ensures Factorial(n) != 0
  ensures Factorial(n) != 0 ==> Factorial(n) / Factorial(n) == 1
{
  FactorialNonZero(n);
  assert Factorial(n) != 0;
}
// </vc-helpers>

// <vc-spec>
method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
// </vc-spec>
// <vc-code>
{
  result := 1;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == Factorial(i - 1)
  {
    result := result * i;
    i := i + 1;
  }
  
  assert i == n + 1;
  assert result == Factorial(n);
}
// </vc-code>

