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
proof fn fib_property(n: nat)
    ensures fib(n + 2) == fib(n + 1) + fib(n)
    decreases n
{
    if n > 0 {
        fib_property((n - 1) as nat);
    }
}

proof fn fib_bounded(n: nat, m: nat)
    requires n <= m
    ensures fib(n) <= fib(m)
    decreases m - n
{
    if n < m {
        fib_bounded(n, (m - 1) as nat);
        if m == 1 {
            assert(fib(0) <= fib(1));
        } else {
            fib_property((m - 2) as nat);
            assert(fib(m) >= fib((m - 1) as nat));
        }
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
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut a = 0;
        let mut b = 1;
        let mut i = 2;
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib((i - 2) as nat),
                b == fib((i - 1) as nat)
            decreases n - i
        {
            let c = a + b;
            a = b;
            b = c;
            proof {
                fib_property((i - 2) as nat);
            }
            i += 1;
        }
        b
    }
}
// </vc-code>

fn main() {}

}