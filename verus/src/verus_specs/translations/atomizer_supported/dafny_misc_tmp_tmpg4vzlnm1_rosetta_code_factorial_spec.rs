// recursive definition of factorial
// ATOM 
// recursive definition of factorial
spec fn factorial(n: nat) -> nat {
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// iterative implementation of factorial
// SPEC 

// iterative implementation of factorial
pub fn iterative_factorial(n: nat) -> (result: nat)
    ensures(result == factorial(n))
{
}