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
#[verifier::proof]
fn fib_add(n: nat)
    requires n > 1
    ensures fib(n) == fib((n as int - 1) as nat) + fib((n as int - 2) as nat)
{
    reveal(fib);
    // Proof follows from the definition of fib
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
        let mut a: nat = 0; // fib(0)
        let mut b: nat = 1; // fib(1)
        let mut i: u64 = 2; // index

        proof {
            assert(n >= 2 && n < 100);
            assert(a == fib(0));
            assert(b == fib(1));
        }

        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib((i as int - 2) as nat),
                b == fib((i as int - 1) as nat),
            decreases (n as int - i as int)
        {
            let next = a + b;
            proof {
                assert(a == fib((i as int - 2) as nat));
                assert(b == fib((i as int - 1) as nat));
                if i > 1 {
                    fib_add(i as nat);
                    assert(fib(i as nat) == fib((i as int - 1) as nat) + fib((i as int - 2) as nat));
                }
                assert(next == a + b);
                assert(next == fib(i as nat));
            }
            a = b;
            b = next;
            i = i + 1;
        }
        proof {
            assert(b == fib(n as nat));
            assert(b >= 0 as nat && b <= 18446744073709551615 as nat);
        }
        (b as int) as u64
    }
}
// </vc-code>

fn main() {}

}