// ATOM 
fn Factorial(n: int) -> int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {
        if n == 0 { 1 }
        else { n * Factorial(n-1) }
    }

// SPEC 

pub fn FactorialOfLastDigit(n: int) -> int
    requires(n >= 0)
    ensures(|fact: int| fact == Factorial(n % 10))
{
}