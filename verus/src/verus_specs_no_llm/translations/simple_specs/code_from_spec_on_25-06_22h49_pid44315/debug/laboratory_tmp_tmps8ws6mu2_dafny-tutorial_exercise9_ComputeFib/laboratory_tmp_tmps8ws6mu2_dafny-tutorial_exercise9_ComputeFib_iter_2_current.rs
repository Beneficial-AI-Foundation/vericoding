use builtin::*;
use builtin_macros::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib((n - 1) as nat) + fib((n - 2) as nat)
    }
}

fn main() {
}

fn ComputeFib(n: nat) -> (b: nat)
    ensures
        b == fib(n) // Do not change this postcondition
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
            prev == fib(i - 2),
            curr == fib(i - 1),
        decreases n - i
    {
        let next = prev + curr;
        
        // Proof that next equals fib(i)
        assert(next == prev + curr);
        assert(prev == fib(i - 2));
        assert(curr == fib(i - 1));
        assert(fib(i) == fib(i - 1) + fib(i - 2)) by {
            assert(i >= 2);
        };
        assert(next == fib(i));
        
        prev = curr;
        curr = next;
        i = i + 1;
    }
    
    // After the loop: i == n + 1, so curr == fib(n)
    assert(i == n + 1);
    assert(curr == fib(i - 1));
    assert(curr == fib(n));
    
    curr
}

}

The key changes I made:





The verification should now succeed because:
- The loop maintains the invariant that `prev` and `curr` hold the correct Fibonacci values
- Each iteration correctly computes the next Fibonacci number
- The final assertion proves that the returned value equals `fib(n)`