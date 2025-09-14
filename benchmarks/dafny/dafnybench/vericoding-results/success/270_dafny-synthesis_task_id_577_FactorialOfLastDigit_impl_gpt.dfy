function Factorial(n: int): int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {
        if n == 0 then 1
        else n * Factorial(n-1)
    }

// <vc-helpers>
lemma ModRange(n:int, m:int)
  requires m > 0
  ensures 0 <= n % m < m
{}
// </vc-helpers>

// <vc-spec>
method FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
// </vc-spec>
// <vc-code>
{
  ModRange(n, 10);
  fact := Factorial(n % 10);
}
// </vc-code>

