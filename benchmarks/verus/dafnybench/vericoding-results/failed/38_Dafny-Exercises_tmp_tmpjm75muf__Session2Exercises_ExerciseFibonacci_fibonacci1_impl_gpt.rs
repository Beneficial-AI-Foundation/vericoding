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

// </vc-helpers>

// <vc-spec>
fn fibonacci1(n: u64) -> (f: u64)
    requires n < 100, // practical bound to prevent overflow
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u64 = 0;
    let mut a: u64 = 0; // fib(0)
    let mut b: u64 = 1; // fib(1)
    while i < n
        invariant i <= n,
                  a == fib(i as nat),
                  b == fib((i as nat) + 1)
        decreases (n - i) as nat
    {
        let old_i = i;
        let old_a = a;
        let old_b = b;

        let next = old_a + old_b;
        a = old_b;
        b = next;
        i = old_i + 1;

        proof {
            let k = old_i as nat;
            assert(k + 2 != 0);
            assert(k + 2 != 1);
            assert(fib(k + 2) == fib(((k + 2) - 1) as nat) + fib(((k + 2) - 2) as nat));
            assert(((k + 2) - 1) as nat == k + 1);
            assert(((k + 2) - 2) as nat == k);
            assert(fib(k + 2) == fib(k + 1) + fib(k));
            assert(i as nat == k + 1);
            assert(a == fib(i as nat));
            assert(b == fib(i as nat + 1));
        }
    }
    a
}
// </vc-code>

fn main() {}

}