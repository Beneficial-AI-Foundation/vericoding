use vstd::prelude::*;

verus! {

// definition of Fibonacci numbers
spec fn fibonacci(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat)
    }
}

// iterative calculation of Fibonacci numbers

// <vc-helpers>
proof fn fibonacci_iterative_correctness(n: nat, a: nat, b: nat, i: nat)
    requires
        n < 100,
        i <= n,
        a == fibonacci(i),
        b == fibonacci(i + 1)
    ensures
        b == fibonacci(i + 1)
    decreases n - i
{
    if i < n {
        fibonacci_iterative_correctness(n, b, (a + b) as nat, i + 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100  // practical bound to prevent overflow
    ensures f == fibonacci(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100
    ensures f == fibonacci(n as nat)
{
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }
    
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    let mut i: u64 = 1;
    
    while i < n
        invariant
            i <= n,
            a == fibonacci(i as nat),
            b == fibonacci((i + 1) as nat)
    {
        let temp = b;
        b = a + b;
        a = temp;
        i = i + 1;
    }
    
    proof {
        fibonacci_iterative_correctness(n as nat, a as nat, b as nat, i as nat);
    }
    
    b
}
// </vc-code>

fn main() {
}

}