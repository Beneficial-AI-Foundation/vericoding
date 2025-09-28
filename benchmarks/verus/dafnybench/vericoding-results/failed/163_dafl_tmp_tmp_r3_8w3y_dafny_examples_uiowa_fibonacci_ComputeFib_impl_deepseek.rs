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
proof fn lemma_fib_mono(x: nat, y: nat)
    requires x <= y,
    ensures fib(x) <= fib(y),
    decreases y
{
    if y == 0 {
        assert(x == 0);
    } else if y == 1 {
        if x == 0 {
            assert(fib(0) == 0 && fib(1) == 1);
        } else {
            assert(x == 1);
        }
    } else {
        if x == y {
        } else {
            lemma_fib_mono(x, (y - 1) as nat);
            assert(fib((y - 2) as nat) <= fib((y - 1) as nat));
            assert(fib(y) == fib((y - 1) as nat) + fib((y - 2) as nat));
        }
    }
}

proof fn lemma_fib_props(n: nat)
    ensures
        if n >= 1 {
            fib((n - 1) as nat) <= fib(n)
        } else {
            true
        },
    decreases n
{
    if n >= 1 {
        if n == 1 {
            assert(fib(0) == 0 && fib(1) == 1);
        } else {
            lemma_fib_props((n - 1) as nat);
            lemma_fib_props((n - 2) as nat);
            assert(fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat));
            assert(fib((n - 1) as nat) <= fib(n));
        }
    }
}

proof fn lemma_fib_identity(n: nat) 
    requires n >= 1,
    ensures fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat),
    decreases n
{
    if n >= 2 {
        // By definition of fib
    } else {
        if n == 1 {
            assert(fib(1) == 1);
            assert(fib(0) + fib((1 - 2) as nat) == 0 + fib(0));
            assert(fib(0) == 0);
        }
    }
}

proof fn lemma_fib_1() 
    ensures fib(1) == 1
{
}

proof fn lemma_fib_0() 
    ensures fib(0) == 0
{
}
// </vc-helpers>

// <vc-spec>
fn ComputeFib(n: usize) -> (f: usize)
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        proof { lemma_fib_0(); }
        return 0;
    }
    let mut a: usize = 0;
    let mut b: usize = 1;
    let mut i: usize = 1;
    
    proof {
        lemma_fib_props(1);
        lemma_fib_1();
        assert(fib(1) == 1);
        assert(fib(0) == 0);
    }
    
    while i < n
        invariant
            1 <= i <= n,
            a == fib((i - 1) as nat),
            b == fib(i as nat),
        decreases n - i
    {
        let next: usize;
        proof {
            lemma_fib_identity((i + 1) as nat);
            assert(fib((i + 1) as nat) == fib(i as nat) + fib((i - 1) as nat));
        }
        next = a + b;
        proof {
            assert(next == fib(i as nat) + fib((i - 1) as nat));
            assert(next == fib((i + 1) as nat));
        }
        a = b;
        b = next;
        i = i + 1;
        
        proof {
            assert(b == fib(i as nat));
            assert(a == fib((i - 1) as nat));
        }
    }
    b
}
// </vc-code>

fn main() {
}

}