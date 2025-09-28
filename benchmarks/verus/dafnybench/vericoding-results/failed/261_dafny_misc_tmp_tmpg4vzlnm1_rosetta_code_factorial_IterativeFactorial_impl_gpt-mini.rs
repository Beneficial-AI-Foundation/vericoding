use vstd::prelude::*;

verus! {

// recursive definition of factorial
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// iterative implementation of factorial

// <vc-helpers>
proof fn factorial_monotone(n: nat, k: nat)
    requires n <= k
    ensures factorial(n) <= factorial(k)
    decreases k
{
    if k == 0 {
        // then n == 0, factorial(0) == factorial(0)
    } else {
        if n == k {
            // equal
        } else {
            // n <= k-1
            factorial_monotone(n, k - 1);
            // factorial(k) = k * factorial(k-1) >= factorial(k-1) since k >= 1
            assert(factorial(k - 1) <= factorial(k));
            assert(factorial(n) <= factorial(k));
        }
    }
}

proof fn factorial_le_u32max(n: nat)
    requires n < 13
    ensures factorial(n) <= u32::MAX as nat
    decreases n
{
    if n == 0 {
        // factorial(0) == 1 <= u32::MAX
    } else {
        // Use monotonicity to bound factorial(n) by factorial(12)
        factorial_monotone(n, 12);
        // Compute factorial(12) (can be evaluated by the verifier)
        assert(factorial(12) == 479001600);
        assert(479001600 <= u32::MAX as nat);
        // hence factorial(n) <= factorial(12) <= u32::MAX
    }
}
// </vc-helpers>

// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 1;
    let mut acc: u32 = 1;

    while i <= n
        invariant 1u32 <= i && i <= n + 1u32 && (acc as nat) == factorial(((i - 1u32) as nat));
        decreases (n as nat) + 1 - (i as nat);
    {
        // compute product in nat to avoid u32 overflow issues, then cast after proving bound
        let prod_nat: nat = (acc as nat) * (i as nat);
        proof {
            // From invariant: acc as nat == factorial(i-1)
            assert((acc as nat) == factorial(((i - 1u32) as nat)));
            // factorial(i) = i * factorial(i-1)
            assert(factorial((i as nat)) == (i as nat) * factorial(((i - 1u32) as nat)));
            // thus prod_nat == factorial(i)
            assert(prod_nat == factorial((i as nat)));
            // and since i <= n and n < 13, factorial(i) <= u32::MAX
            factorial_le_u32max((n as nat));
            factorial_monotone((i as nat), (n as nat));
            assert(factorial((i as nat)) <= u32::MAX as nat);
            assert(prod_nat <= u32::MAX as nat);
        }
        acc = prod_nat as u32;
        i = i + 1u32;
    }

    acc
}
// </vc-code>

fn main() {}

}