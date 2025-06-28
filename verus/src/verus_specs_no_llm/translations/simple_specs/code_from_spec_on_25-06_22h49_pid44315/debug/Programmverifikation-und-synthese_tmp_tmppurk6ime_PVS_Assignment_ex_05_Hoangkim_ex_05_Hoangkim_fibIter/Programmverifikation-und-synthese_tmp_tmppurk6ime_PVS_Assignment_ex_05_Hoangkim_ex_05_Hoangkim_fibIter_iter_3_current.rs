use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fib(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 } else if n == 1 { 1 } else { fib(n - 1) + fib(n - 2) }
}

fn fib_iter(n: nat) -> (a: nat)
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
            2 <= i <= n + 1,
            prev == fib(i - 2),
            curr == fib(i - 1),
            n >= 2
        decreases n + 1 - i
    {
        let next = prev + curr;
        
        // Prove that next equals fib(i)
        assert(next == fib(i - 2) + fib(i - 1));
        assert(i >= 2);
        assert(next == fib(i)) by {
            // The definition of fib(i) when i >= 2 is fib(i-1) + fib(i-2)
            assert(fib(i) == fib(i - 1) + fib(i - 2));
        };
        
        prev = curr;
        curr = next;
        i = i + 1;
    }
    
    assert(i == n + 1);
    assert(curr == fib(n));
    curr
}

}