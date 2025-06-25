// definition of Fibonacci numbers
// ATOM 
// definition of Fibonacci numbers
spec fn Fibonacci(n: nat) -> nat {
    match n {
        0 => 0,
        1 => 1,
        _ => Fibonacci((n - 1) as nat) + Fibonacci((n - 2) as nat),
    }
}

// iterative calculation of Fibonacci numbers
// SPEC 

// iterative calculation of Fibonacci numbers
pub fn FibonacciIterative(n: nat) -> (f: nat)
    ensures(f == Fibonacci(n))
{
}