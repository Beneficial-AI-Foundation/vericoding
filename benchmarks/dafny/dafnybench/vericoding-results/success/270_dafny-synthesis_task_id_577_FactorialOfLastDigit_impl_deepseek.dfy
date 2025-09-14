function Factorial(n: int): int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {
        if n == 0 then 1
        else n * Factorial(n-1)
    }

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
// </vc-spec>
// <vc-code>
{
  var lastDigit := n % 10;
  fact := 1;
  var i := 1;
  while i <= lastDigit
    invariant 1 <= i <= lastDigit + 1
    invariant fact == Factorial(i - 1)
  {
    fact := fact * i;
    i := i + 1;
  }
}
// </vc-code>

