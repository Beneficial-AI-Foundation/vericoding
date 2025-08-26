// - The `Factorial` function is defined for all non-negative integers
// - So `Factorial(n % 10)` is well-defined and will satisfy the postcondition

// <vc-spec>
function Factorial(n: int): int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {
        if n == 0 then 1
        else n * Factorial(n-1)
    }

// <vc-helpers>
// </vc-helpers>

method FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
// </vc-spec>
// <vc-code>
{
  fact := Factorial(n % 10);
}
// </vc-code>