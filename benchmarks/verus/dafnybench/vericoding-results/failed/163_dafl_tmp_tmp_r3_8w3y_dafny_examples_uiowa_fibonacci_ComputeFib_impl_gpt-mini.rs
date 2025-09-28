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
proof fn lemma_fib_unfold(k: nat)
    requires k >= 2
    ensures fib(k) == fib((k - 1) as nat) + fib((k - 2) as nat)
    decreases k
{
    // unfold definition of fib; since k >= 2, the else branch applies
    assert(fib(k) == if k == 0 { 0 } else if k == 1 { 1 } else { fib((k - 1) as nat) + fib((k - 2) as nat) });
    // conclude the desired equality
    assert(fib(k) == fib((k - 1) as nat) + fib((k - 2) as nat));
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
        let mut i: usize = 2;
        let mut prev: usize = 0; // fib(0)
        let mut curr: usize = 1; // fib(1)
        while i <= n
            invariant i >= 2 && i <= n + 1 && (prev as nat) == fib((i - 2) as nat) && (curr as nat) == fib((i - 1) as nat)
            decreases (n + 1) - i
        {
            let next: usize = prev + curr;
            proof {
                assert(i >= 2);
                assert((prev as nat) == fib((i - 2) as nat));
                assert((curr as nat) == fib((i - 1) as nat));
                // next as nat == (prev as nat) + (curr as nat)
                assert((next as nat) == (prev as nat) + (curr as nat));
                // use lemma to unfold fib(i)
                lemma_fib_unfold(i as nat);
                // combine equalities to conclude next == fib(i)
                assert((next as nat) == fib(i as nat));
            }
            prev = curr;
            curr = next;
            i = i + 1;
        }
        curr
    }
}
// </vc-code>

fn main() {
}

}