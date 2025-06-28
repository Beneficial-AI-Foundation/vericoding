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
            i >= 2,
            i <= n + 1,
            prev == fib((i - 2) as nat),
            curr == fib((i - 1) as nat),
        decreases n - i
    {
        let next = prev + curr;
        prev = curr;
        curr = next;
        i = i + 1;
        
        assert(prev == fib((i - 2) as nat));
        assert(curr == fib((i - 1) as nat));
    }
    
    curr
}

}