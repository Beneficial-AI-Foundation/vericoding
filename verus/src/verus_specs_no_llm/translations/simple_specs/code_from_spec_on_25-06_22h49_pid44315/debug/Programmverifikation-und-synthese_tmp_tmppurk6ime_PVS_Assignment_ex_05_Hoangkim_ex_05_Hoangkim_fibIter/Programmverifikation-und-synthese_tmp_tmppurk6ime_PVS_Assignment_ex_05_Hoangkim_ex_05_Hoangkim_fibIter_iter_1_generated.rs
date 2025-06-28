use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fib(n: nat) -> nat 
    decreases n
{
    if n <= 1 { n } else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

fn fibIter(n: nat) -> (a: nat)
    requires
        n > 0
    ensures
        a == fib(n)
{
    if n == 1 {
        return 1;
    }
    
    let mut prev = 0nat;
    let mut curr = 1nat;
    let mut i = 2nat;
    
    while i <= n 
        invariant
            i >= 2,
            i <= n + 1,
            prev == fib((i - 2) as nat),
            curr == fib((i - 1) as nat)
        decreases n - i
    {
        let next = prev + curr;
        prev = curr;
        curr = next;
        i = i + 1;
    }
    
    curr
}

}

The key aspects of this implementation:



   - `i >= 2`: maintains that we're past the base cases
   - `i <= n + 1`: bounds check for termination
   - `prev == fib((i - 2) as nat)`: `prev` holds the (i-2)th Fibonacci number
   - `curr == fib((i - 1) as nat)`: `curr` holds the (i-1)th Fibonacci number



The invariants ensure that after the loop terminates (when i == n + 1), `curr` contains `fib(n)`, satisfying the postcondition.