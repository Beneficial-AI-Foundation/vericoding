use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

// <vc-helpers>
// Helper lemma to establish the relationship between consecutive Fibonacci values
proof fn fib_step_lemma(n: nat)
    requires n >= 2,
    ensures fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat),
{
    // This follows directly from the definition of fib for n >= 2
}
// </vc-helpers>

// <vc-spec>
fn fibonacci1(n: u64) -> (f: u64)
    requires n < 100, // practical bound to prevent overflow
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 1;
    }
    
    let mut prev2: u64 = 0;  // fib(0)
    let mut prev1: u64 = 1;  // fib(1)
    let mut i: u64 = 2;
    
    while i <= n
        invariant
            2 <= i <= n + 1,
            prev2 == fib((i - 2) as nat),
            prev1 == fib((i - 1) as nat),
        decreases n - i + 1,
    {
        let current = prev1 + prev2;
        prev2 = prev1;
        prev1 = current;
        i = i + 1;
    }
    
    prev1
}
// </vc-code>

fn main() {}

}