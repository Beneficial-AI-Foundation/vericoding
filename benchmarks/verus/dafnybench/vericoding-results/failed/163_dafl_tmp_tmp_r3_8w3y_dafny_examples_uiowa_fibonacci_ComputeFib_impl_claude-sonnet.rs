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
proof fn lemma_fib_properties(n: nat)
    ensures n >= 2 ==> fib(n) == fib(n - 1) + fib(n - 2)
    ensures fib(0) == 0
    ensures fib(1) == 1
    decreases n
{
    if n >= 2 {
        assert(fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat));
        assert(fib((n - 1) as nat) == fib(n - 1));
        assert(fib((n - 2) as nat) == fib(n - 2));
    }
}

proof fn lemma_fib_monotonic(i: nat, j: nat)
    requires i <= j
    ensures fib(i) <= fib(j)
    decreases j - i
{
    if i == j {
        return;
    }
    if j == 0 {
        return;
    }
    if j == 1 {
        if i == 0 {
            assert(fib(0) == 0);
            assert(fib(1) == 1);
        }
        return;
    }
    
    lemma_fib_monotonic(i, j - 1);
    lemma_fib_monotonic(j - 2, j - 1);
    lemma_fib_properties(j);
    
    if i <= j - 1 {
        assert(fib(i) <= fib(j - 1));
        assert(fib(j - 1) <= fib(j - 1) + fib(j - 2));
        assert(fib(j) == fib(j - 1) + fib(j - 2));
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
    
    let mut a: usize = 0;
    let mut b: usize = 1;
    let mut i: usize = 2;
    
    while i <= n
        invariant
            i >= 2,
            i <= n + 1,
            a == fib((i - 2) as nat),
            b == fib((i - 1) as nat)
    {
        proof {
            lemma_fib_properties(i as nat);
        }
        
        let temp = a + b;
        a = b;
        b = temp;
        i = i + 1;
        
        assert(a == fib((i - 2) as nat));
        assert(b == fib((i - 1) as nat));
    }
    
    b
}
// </vc-code>

fn main() {
}

}