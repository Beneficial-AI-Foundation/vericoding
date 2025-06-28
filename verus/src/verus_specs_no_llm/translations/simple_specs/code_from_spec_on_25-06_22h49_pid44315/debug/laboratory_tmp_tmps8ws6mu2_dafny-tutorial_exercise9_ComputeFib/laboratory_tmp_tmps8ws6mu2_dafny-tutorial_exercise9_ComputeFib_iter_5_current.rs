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
    
    let mut prev: nat = 0;
    let mut curr: nat = 1;
    let mut i: nat = 2;
    
    // At this point we know n >= 2
    assert(n >= 2);
    
    while i <= n
        invariant
            2 <= i <= n + 1,
            prev == fib((i - 2) as nat),
            curr == fib((i - 1) as nat),
        decreases n - i
    {
        // Prove that we can compute fib(i)
        assert(i >= 2);
        assert(fib(i) == fib((i - 1) as nat) + fib((i - 2) as nat)) by {
            // The definition of fib for i >= 2 automatically holds
        };
        
        let next: nat = prev + curr;
        
        // Prove that next equals fib(i)
        assert(next == prev + curr);
        assert(prev == fib((i - 2) as nat));
        assert(curr == fib((i - 1) as nat));
        assert(next == fib((i - 2) as nat) + fib((i - 1) as nat));
        assert(next == fib(i));
        
        prev = curr;
        curr = next;
        i = i + 1;
    }
    
    // After the loop: i == n + 1, so curr == fib(n)
    assert(i == n + 1);
    assert(curr == fib((i - 1) as nat));
    assert(curr == fib(n));
    
    curr
}

}