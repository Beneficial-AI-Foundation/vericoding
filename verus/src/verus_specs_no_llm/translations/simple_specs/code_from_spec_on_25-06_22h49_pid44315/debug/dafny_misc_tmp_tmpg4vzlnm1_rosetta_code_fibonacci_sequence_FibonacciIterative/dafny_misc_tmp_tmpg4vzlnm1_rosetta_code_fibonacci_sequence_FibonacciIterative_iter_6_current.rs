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
            curr == Fibonacci(i - 1),
            n >= 2
    {
        let next = prev + curr;
        
        // Proof that next equals Fibonacci(i)
        assert(next == prev + curr);
        assert(prev == Fibonacci(i - 2));
        assert(curr == Fibonacci(i - 1));
        assert(i >= 2);
        
        // The key insight: since i >= 2, by definition of Fibonacci
        assert(Fibonacci(i) == Fibonacci(i - 1) + Fibonacci(i - 2));
        assert(next == Fibonacci(i));
        
        prev = curr;
        curr = next;
        i = i + 1;
    }
    
    // When loop exits, i == n + 1
    // From invariant: curr == Fibonacci(i - 1) and i == n + 1
    // Therefore: curr == Fibonacci(n)
    assert(i == n + 1);
    assert(curr == Fibonacci(i - 1));
    assert(curr == Fibonacci(n));
    
    curr
}

}