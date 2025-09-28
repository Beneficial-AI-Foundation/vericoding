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
proof fn fib_rec_close(n: nat)
    requires n >= 2
    ensures fib(n) == fib((n-1) as nat) + fib((n-2) as nat)
    decreases n
{
    if n == 2 {
        assert(fib(2) == fib(1) + fib(0));
        assert(fib(1) == 1);
        assert(fib(0) == 0);
    } else {
        fib_rec_close((n-1) as nat);
        fib_rec_close((n-2) as nat);
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
        return 0;
    }
    if n == 1 {
        return 1;
    }
    let mut prevprev: Nat = 0nat;
    let mut prev: Nat = 1nat;
    let mut k: usize = 2;
    while k < n
        invariant
            2 <= k <= n,
            prevprev == fib((k - 2) as nat),
            prev == fib((k - 1) as nat),
        decreases n - k
    {
        proof {
            fib_rec_close(k as nat);
        }
        let tmp: Nat = prevprev + prev;
        prevprev = prev;
        prev = tmp;
        k = k + 1;
    }
    proof {
        fib_rec_close(n as nat);
    }
    let sum: Nat = prevprev + prev;
    #[verifier::truncate]
    sum.into()
}
// </vc-code>

fn main() {
}

}