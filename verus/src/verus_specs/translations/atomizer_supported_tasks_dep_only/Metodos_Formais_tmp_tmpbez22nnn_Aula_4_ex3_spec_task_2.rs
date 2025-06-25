// ATOM 
spec fn Fib(n: nat) -> nat
{
    if n < 2 {
        n
    } else {
        Fib(n-2) + Fib(n-1)
    }
}

// SPEC 

pub fn ComputeFib(n: nat) -> (x: nat)
    ensures x == Fib(n)
{
}

// SPEC 

pub fn Teste()
{
}