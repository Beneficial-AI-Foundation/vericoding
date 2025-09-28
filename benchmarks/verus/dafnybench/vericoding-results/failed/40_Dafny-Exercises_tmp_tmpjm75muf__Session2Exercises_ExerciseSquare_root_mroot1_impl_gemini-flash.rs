use vstd::prelude::*;

verus! {

// <vc-helpers>
fn sqrt_asserts(k: u32, n: u32)
    requires
        (k as int) * (k as int) <= n as int,
        2 * (k as int) + 1 <= (n as int - k as int * k as int),
    ensures
        ((k + 1) as int) * ((k + 1) as int) <= n as int,
{
    proof {
        assert((k as int) * (k as int) + 2 * (k as int) + 1 <= n as int) by {
            assert(2 * (k as int) + 1 <= (n as int - k as int * k as int));
            assert((k as int) * (k as int) + (2 * (k as int) + 1) <= (k as int * k as int) + (n as int - k as int * k as int));
        }
        // This assertion is a tautology, but Verus needs some help with integer arithmetic
        assert((k as int) * (k as int) + 2 * (k as int) + 1 == (k * k + 2 * k + 1) as int);
        assert((k * k + 2 * k + 1) as int == ((k + 1) * (k + 1)) as int);
        assert(((k + 1) * (k + 1)) as int == ((k + 1) as int) * ((k + 1) as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn mroot1(n: u32) -> (r: u32) //Cost O(root n)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// <vc-code>
{
    let mut r: u32 = 0;
    while (r as u64 + 1) * (r as u64 + 1) <= n as u64
        invariant
            (r as int) * (r as int) <= n as int,
            r >= 0,
            n >= 0,
            // (r as u64 + 1) * (r as u64 + 1) doesn't overflow
            (r as u64 + 1) <= 0xFFFF_FFFF && (r as u64 + 1) * (r as u64 + 1) <= 0xFFFF_FFFF,
        decreases n - (r as u64) * (r as u64)
    {
        // Prove ((r + 1) as int) * ((r + 1) as int) <= n as int
        proof {
            let r_as_int = r as int;
            let n_as_int = n as int;

            // From loop condition: (r as u64 + 1) * (r as u64 + 1) <= n as u64
            // This means (r_as_int + 1) * (r_as_int + 1) <= n_as_int
            assert((r as u64 + 1) * (r as u64 + 1) == ((r + 1) as u64) * ((r + 1) as u64));
            assert(((r + 1) as u64) * ((r + 1) as u64) <= n as u64);
            assert(((r + 1) as int) * ((r + 1) as int) <= n as int);
        }
        r = r + 1;
    }
    r
}
// </vc-code>

fn main() {}

}