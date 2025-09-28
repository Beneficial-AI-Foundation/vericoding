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
proof fn lemma_fib_values()
    ensures
        fib(0) == 0,
        fib(1) == 1,
        forall|i: nat| #[trigger] fib(i) == fib((i - 1) as nat) + fib((i - 2) as nat) when i >= 2
{
    assert(fib(0) == 0);
    assert(fib(1) == 1);
}

proof fn lemma_fib_monotonic(i: nat)
    requires
        i >= 2,
    ensures
        (i - 1) as nat == i - 1,
        (i - 2) as nat == i - 2
{
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
        let mut a: u64 = 0;
        let mut b: u64 = 1;
        let mut i: u64 = 2;
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib((i - 2) as nat),
                b == fib((i - 1) as nat),
            decreases n - i
        {
            let next = a + b;
            proof {
                lemma_fib_monotonic(i as nat);
                lemma_fib_values();
                assert(fib(i as nat) == fib((i as nat - 1) as nat) + fib((i as nat - 2) as nat));
                assert(next == fib((i - 2) as nat) + fib((i - 1) as nat));
                assert(next == fib(i as nat));
            }
            a = b;
            b = next;
            i += 1;
            proof {
                lemma_fib_monotonic(i as nat);
            }
        }
        b
    }
}
// </vc-code>

fn main() {}

}