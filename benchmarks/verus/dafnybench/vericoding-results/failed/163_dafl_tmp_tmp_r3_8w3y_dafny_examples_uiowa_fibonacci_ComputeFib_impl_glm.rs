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
proof fn fib_properties()
    ensures
        forall|n: nat| n >= 1 ==> fib(n) >= 1,
        forall|n: nat| n >= 2 ==> fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat),
{
    assert forall|n: nat| n >= 1 ==> fib(n) >= 1 by {
        if n == 1 {
            assert(fib(1) == 1);
        } else {
            assert(fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat));
            assert(fib((n - 1) as nat) >= 1 && fib((n - 2) as nat) >= 1);
        }
    }
    assert forall|n: nat| n >= 2 ==> fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat) by {
        // Property holds by definition of fib for n >= 2
    }
}
// </vc-helpers>

// <vc-spec>
fn ComputeFib(n: usize) -> (f: usize)
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut a: usize = 0;
        let mut b: usize = 1;
        let mut i: usize = 2;
        
        proof {
            fib_properties();
        }
        
        while i <= n
            invariant
                i >= 2,
                i <= n + 1,
                a == fib((i - 2) as nat),
                b == fib((i - 1) as nat),
            decreases n - i
        {
            let next = a + b;
            a = b;
            b = next;
            i = i + 1;
        }
        
        b
    }
}
// </vc-code>

fn main() {
}

}