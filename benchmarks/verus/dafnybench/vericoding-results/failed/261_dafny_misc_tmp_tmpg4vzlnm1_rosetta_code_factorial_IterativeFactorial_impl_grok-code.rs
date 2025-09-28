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
// Empty at this point, no updates needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut res: u64 = 1;
    let mut ii: u32 = 1;
    while ii <= n
        invariant
            1 <= ii <= n + 1,
            res == factorial((ii - 1) as nat)
        decreases ((n as int) - (ii as int))
    {
        proof {
            assert(factorial(ii as nat) == (ii as nat) * factorial((ii - 1) as nat));
            assert(res == factorial((ii - 1) as nat));
        }
        res = res * (ii as u64);
        ii = ii + 1;
    }
    proof { assert(res <= 479001600); }
    res as u32
}
// </vc-code>

fn main() {}

}