// ATOM 
spec fn fib(n: nat) -> nat {
    if n < 2 {
        n
    } else {
        fib(n - 2) + fib(n - 1)
    }
}

// SPEC 
pub fn compute_fib(n: nat) -> (x: nat)
    ensures x == fib(n)
{
}

// SPEC 
pub fn teste()
{
}