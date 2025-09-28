use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// <vc-helpers>
fn factorial_i32_natural_number(n: i32) -> (res: u32)
    requires 0 <= n,
    ensures res == factorial(n as nat),
    decreases n
{
    if n == 0 {
        1
    } else {
        let n_minus_1 = n - 1;
        let rec_call_val = factorial_i32_natural_number(n_minus_1);
        proof {
            assert((n as nat) == (n_minus_1 as nat) + 1);
            assert(factorial(n as nat) == (n as nat) * factorial(n_minus_1 as nat));
            assert(factorial(n as nat) == (n as u32) * rec_call_val);
        }
        (n as u32) * rec_call_val
    }
}
spec fn current_factorial_fits_u32(val: u32) -> bool {
    factorial(val as nat) <= 0xffffffff
}
// </vc-helpers>

// <vc-spec>
fn compute_factorial(n: i32) -> (u: i32)
    requires 1 <= n,
    ensures u == factorial(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut res: u32 = 1;
    let mut i: u32 = 1;

    while i <= n as u32
        invariant
            1 <= i && i <= n as u32 + 1,
            // Assuming that for all i in [1, n], factorial(i-1) fits in u32
            // And that factorial(n) fits in i32 (and thus u32)
            res == factorial((i - 1) as nat),
            0 <= i, // This is redundant given 1 <= i
            current_factorial_fits_u32(i), // Add this invariant to ensure the next factorial computation fits
        decreases (n as u32) - i
    {
        // Prove that the next value of res will not overflow u32
        // This implicitly assumes 0 < i, which is covered by `1 <= i` invariant
        // Also it implicitly assumes that factorial(i) fits in u32
        proof {
            assert(current_factorial_fits_u32(i)); // This assertion is now valid due to the invariant
            assert(res == factorial((i - 1) as nat));
            assert(factorial(i as nat) == factorial((i - 1) as nat) * (i as nat));
            assert(factorial(i as nat) == res * (i as u32) as nat);
        }
        res = res * i;
        i = i + 1;
    }
    proof {
        assert(i == n as u32 + 1);
        assert(res == factorial((i - 1) as nat));
        assert(res == factorial(n as nat));
    }
    res as i32
}
// </vc-code>

fn main() {
}

}