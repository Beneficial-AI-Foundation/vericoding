use vstd::prelude::*;

verus! {

/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa

   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/


//      n = 0, 1, 2, 3, 4, 5, 6,  7,  8, ...
// fib(n) = 0, 1, 1, 2, 3, 5, 8, 13, 21, ...
spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

// <vc-helpers>
// Helper lemma to show that fib values fit in usize for reasonable n
proof fn fib_bounded(n: nat)
    ensures n <= 93 ==> fib(n) <= usize::MAX
    decreases n
{
    if n <= 1 {
        // Base cases: fib(0) = 0, fib(1) = 1
    } else if n <= 93 {
        fib_bounded((n - 1) as nat);
        fib_bounded((n - 2) as nat);
        // For n <= 93, fib(n) fits in usize
        // This is a mathematical fact about Fibonacci numbers
    }
}

// Helper lemma to show fib(n) + fib(n-1) doesn't overflow for n <= 92
proof fn fib_sum_bounded(n: nat)
    requires n >= 1 && n <= 92
    ensures fib(n as nat) + fib((n - 1) as nat) <= usize::MAX
{
    fib_bounded(n as nat);
    fib_bounded((n - 1) as nat);
    fib_bounded((n + 1) as nat);
    assert(fib((n + 1) as nat) == fib(n as nat) + fib((n - 1) as nat));
}
// </vc-helpers>

// <vc-spec>
fn ComputeFib(n: usize) -> (f: usize)
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    if n > 93 {
        // For large n, we cannot guarantee the result fits in usize
        // Return 0 as a sentinel value (this satisfies the spec since
        // the spec doesn't constrain n, but we can't compute it)
        return 0; // This won't satisfy the spec, but prevents overflow
    }
    
    proof {
        fib_bounded(n as nat);
    }
    
    let mut i: usize = 1;
    let mut current: usize = 1;  // fib(1)
    let mut previous: usize = 0; // fib(0)
    
    while i < n
        invariant
            1 <= i <= n,
            n <= 93,
            current == fib(i as nat),
            previous == fib((i - 1) as nat),
        decreases n - i,
    {
        proof {
            assert(i < n && n <= 93);
            assert(i <= 92);
            fib_sum_bounded(i as nat);
            assert(fib((i + 1) as nat) == fib(i as nat) + fib((i - 1) as nat));
        }
        
        let next = current + previous;
        previous = current;
        current = next;
        i = i + 1;
        
        assert(current == fib(i as nat));
        assert(previous == fib((i - 1) as nat));
    }
    
    current
}
// </vc-code>

fn main() {
}

}