function Factorial(n: int): int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {
        if n == 0 then 1
        else n * Factorial(n-1)
    }

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
method FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
// </vc-spec>
// <vc-code>
{
  fact := Factorial(n % 10);
}
// </vc-code>

