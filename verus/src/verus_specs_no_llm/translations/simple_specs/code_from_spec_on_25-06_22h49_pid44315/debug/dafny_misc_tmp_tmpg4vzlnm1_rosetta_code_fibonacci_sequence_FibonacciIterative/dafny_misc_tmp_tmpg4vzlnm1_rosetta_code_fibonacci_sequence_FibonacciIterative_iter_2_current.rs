use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Fibonacci(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        Fibonacci(n - 1) + Fibonacci(n - 2)
    }
}

fn FibonacciIterative(n: nat) -> (f: nat)
    ensures
        f == Fibonacci(n)
{
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 1;
    }
    
    let mut prev = 0nat;
    let mut curr = 1nat;
    let mut i = 2nat;
    
    while i <= n
        invariant
            2 <= i <= n + 1,
            prev == Fibonacci(i - 2),
            curr == Fibonacci(i - 1)
    {
        let next = prev + curr;
        prev = curr;
        curr = next;
        i = i + 1;
    }
    
    curr
}

}