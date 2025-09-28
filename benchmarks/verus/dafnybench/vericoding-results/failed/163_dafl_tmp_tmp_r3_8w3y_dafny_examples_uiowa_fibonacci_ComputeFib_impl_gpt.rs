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
proof fn fib_step(n: nat)
    ensures fib((n + 2) as nat) == fib((n + 1) as nat) + fib(n)
{
    let m = (n + 2) as nat;
    assert(m >= 2);
    assert(fib(m) == fib((m - 1) as nat) + fib((m - 2) as nat));
    assert((m - 1) as nat == (n + 1) as nat);
    assert((m - 2) as nat == n);
    assert(fib((n + 2) as nat) == fib((n + 1) as nat) + fib(n));
}
// </vc-helpers>

// <vc-spec>
fn ComputeFib(n: usize) -> (f: usize)
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut a: usize = 0;
    let mut b: usize = 1;

    while i < n
        invariant
            i <= n,
            a == fib(i as nat),
            b == fib(((i as nat) + 1) as nat),
    {
        let ii = i;
        let ai = a;
        let bi = b;

        assert(ai == fib(ii as nat));
        assert(bi == fib(((ii as nat) + 1) as nat));

        proof {
            fib_step(ii as nat);
        }

        let next = ai + bi;

        a = bi;
        b = next;
        i = ii + 1;

        assert(ii < n);
        assert(i <= n);

        assert(ii + 1 == i);
        assert(a == bi);
        assert(bi == fib(((ii as nat) + 1) as nat));
        assert(a == fib(i as nat));

        assert(next == ai + bi);
        assert(ai + bi == fib(((ii as nat) + 1) as nat) + fib(ii as nat));
        assert(fib(((ii as nat) + 2) as nat) == fib(((ii as nat) + 1) as nat) + fib(ii as nat));
        assert(next == fib(((ii as nat) + 2) as nat));

        assert((((i as nat) + 1) as nat) == (((ii as nat) + 2) as nat));
        assert(b == fib(((i as nat) + 1) as nat));
    }

    assert(i >= n);
    assert(i <= n);
    assert(i == n);
    assert(a == fib(n as nat));
    a
}
// </vc-code>

fn main() {
}

}