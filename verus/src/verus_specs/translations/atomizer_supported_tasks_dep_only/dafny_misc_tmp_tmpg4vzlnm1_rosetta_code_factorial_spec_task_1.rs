spec fn Factorial(n: nat) -> nat {
    if n == 0 { 1 } else { n * Factorial((n - 1) as nat) }
}

pub fn IterativeFactorial(n: nat) -> (result: nat)
    ensures result == Factorial(n)
{
}