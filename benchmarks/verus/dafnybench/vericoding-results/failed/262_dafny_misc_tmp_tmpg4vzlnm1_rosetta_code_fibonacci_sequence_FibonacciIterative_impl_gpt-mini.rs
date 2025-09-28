use vstd::prelude::*;

verus! {

// definition of Fibonacci numbers
spec fn fibonacci(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat)
    }
}

// iterative calculation of Fibonacci numbers

// <vc-helpers>
proof fn fib_plus(n: nat)
    ensures fibonacci(n + 2) == fibonacci(n + 1) + fibonacci(n)
    decreases n
{
    if n == 0 {
        // fibonacci(2) == fibonacci(1) + fibonacci(0)
        assert(fibonacci(2) == 1);
        assert(fibonacci(1) + fibonacci(0) == 1);
    } else {
        fib_plus(n - 1);
        // after the recursive call we can unfold the definition once to get the desired property
        // for n > 0 the definition of fibonacci gives the result
    }
}
// </vc-helpers>

// <vc-spec>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100  // practical bound to prevent overflow
    ensures f == fibonacci(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u64 = 0;
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    while i < n
        invariant i <= n && a == (fibonacci(i as nat) as u64) && b == (fibonacci((i as nat) + 1) as u64);
        decreases ((n - i) as nat)
    {
        // save old values
        let i_old = i;
        let a_old = a;
        let b_old = b;

        // compute next pair (f(i+1), f(i+2))
        let tmp = a + b;
        // update
        a = b_old;
        b = tmp;
        i = i + 1;

        // show invariants preserved
        proof {
            // k is the old i as nat
            let k: nat = (i_old as nat);

            // From the loop invariant before the update:
            // a_old == fibonacci(k) as u64
            // b_old == fibonacci(k + 1) as u64
            assert(a_old == (fibonacci(k) as u64));
            assert(b_old == (fibonacci(k + 1) as u64));

            // a after update equals previous b
            assert(a == b_old);
            assert(a == (fibonacci(k + 1) as u64));
            // and since i = i_old + 1, we have a == fibonacci(i as nat)
            assert(a == (fibonacci(i as nat) as u64));

            // b after update equals a_old + b_old
            assert(b == a_old + b_old);

            // convert the sum of u64s to the sum of nats cast to u64
            assert(a_old + b_old == ((fibonacci(k) as u64) + (fibonacci(k + 1) as u64)));

            // use fib_plus to relate fibonacci(k+2) to fibonacci(k+1) + fibonacci(k)
            fib_plus(k);
            assert((fibonacci(k + 1) + fibonacci(k)) as u64 == (fibonacci(k + 2) as u64));

            // combine the equalities to conclude b == fibonacci(k+2) as u64
            assert(b == (fibonacci(k + 2) as u64));

            // relate k+2 to (i as nat) + 1: since i = i_old + 1, k = i_old as nat, so k+2 = (i as nat) + 1
            assert((k + 2) == ((i as nat) + 1));
            assert(b == (fibonacci((i as nat) + 1) as u64));
        }
    }
    a
}
// </vc-code>

fn main() {
}

}