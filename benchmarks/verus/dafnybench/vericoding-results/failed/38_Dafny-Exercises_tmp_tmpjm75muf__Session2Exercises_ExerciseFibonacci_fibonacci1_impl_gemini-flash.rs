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
fn fib_auto_induction_1_0(n: nat)
    requires n > 1
    ensures fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat)
{
    // No code needed, this is for auto-induction
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
        return 0;
    } else if n == 1 {
        return 1;
    }

    let mut a: u64 = 0;
    let mut b: u64 = 1;
    let mut i: u64 = 2;

    while i <= n
        invariant
            i <= n + 1,
            a == fib((i - 2) as nat),
            b == fib((i - 1) as nat),
            n < 100, // preserve n property
            i >= 2, // Ensure i is at least 2 for (i-2) and (i-1)
            b.checked_add(a).is_some(), // Ensure a + b does not overflow
            (b + a) as nat == fib(i as nat) // Add invariant to track fib(i)
        decreases (n - i)
    {
        // Proof that i >= 2 implies i-2 and i-1 are valid for fib
        // (i-2) as nat is fine because i >= 2
        // (i-1) as nat is fine because i >= 2
        // No explicit proof needed for fib property, Verus handles it via definition.

        let next_b = a + b;
        a = b;
        b = next_b;

        i = i + 1;
    }

    // After the loop, i == n + 1
    // So, a == fib((n + 1 - 2) as nat) == fib(n as nat)
    // and b == fib((n + 1 - 1) as nat) == fib(n as nat)
    // Thus, b is the (n)th fib number.
    b
}
// </vc-code>

fn main() {}

}