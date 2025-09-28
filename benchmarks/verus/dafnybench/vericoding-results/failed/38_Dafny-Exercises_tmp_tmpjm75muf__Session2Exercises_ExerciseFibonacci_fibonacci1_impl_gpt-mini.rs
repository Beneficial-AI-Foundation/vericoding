use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

// <vc-helpers>
spec fn lemma_fib_add(n: nat) -> ()
    ensures fib(n + 2) == fib(n + 1) + fib(n)
    decreases n
{
    if n == 0 {
        // fib(2) == 1, fib(1) + fib(0) == 1 + 0 == 1
        assert(fib(2) == fib(1) + fib(0));
    } else if n == 1 {
        // fib(3) == 2, fib(2) + fib(1) == 1 + 1 == 2
        assert(fib(3) == fib(2) + fib(1));
    } else {
        // For n >= 2, by definition fib(m) = fib(m-1) + fib(m-2)
        // so fib(n+2) = fib((n+2)-1) + fib((n+2)-2) = fib(n+1) + fib(n)
        assert(fib(n + 2) == fib((n + 2) - 1) + fib((n + 2) - 2));
    }
}
// </vc-helpers>

// <vc-spec>
fn fibonacci1(n: u64) -> (f: u64)
    requires n < 100, // practical bound to prevent overflow
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    let N: nat = n as nat;
    let mut i: nat = 0;
    let mut a: nat = 0;
    let mut b: nat = 1;
    while i < N
        invariant i <= N;
        invariant a == fib(i);
        invariant b == fib(i + 1);
        decreases N - i;
    {
        let ai = a;
        let bi = b;
        let ii = i;
        // update logical variables
        a = bi;
        b = ai + bi;
        i = i + 1;
        proof {
            // preserve invariants using lemma
            assert(ai == fib(ii));
            assert(bi == fib(ii + 1));
            lemma_fib_add(ii);
            // a == fib(i)
            assert(a == bi);
            assert(i == ii + 1);
            assert(a == fib(i));
            // b == fib(i + 1)
            assert(b == ai + bi);
            assert(b == fib(ii + 2));
            assert(b == fib(i + 1));
        }
    }
    (a as u64)
}
// </vc-code>

fn main() {}

}