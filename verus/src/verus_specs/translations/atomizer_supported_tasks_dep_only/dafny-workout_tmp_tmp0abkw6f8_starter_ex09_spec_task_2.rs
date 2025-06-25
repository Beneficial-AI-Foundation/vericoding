// ATOM 
spec fn fib(n: nat) -> nat
{
    if n == 0 { 0 } else
    if n == 1 { 1 } else {
        fib((n - 1) as nat) + fib((n - 2) as nat)
    }
}

// SPEC 

pub fn ComputeFib(n: nat) -> (b: nat)
    ensures(b == fib(n))
{
}

// SPEC 

pub fn Main()
{
}