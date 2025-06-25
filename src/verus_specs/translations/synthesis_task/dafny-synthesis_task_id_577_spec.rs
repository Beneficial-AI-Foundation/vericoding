// ATOM
spec fn Factorial(n: int) -> int
    recommends n >= 0
{
    if n == 0 { 1 } else { n * Factorial(n-1) }
}

// SPEC
pub fn FactorialOfLastDigit(n: int) -> (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
{
}