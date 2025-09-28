// <vc-preamble>
use vstd::prelude::*;

verus!{

spec fn triangle(n: nat) -> (result: nat)
    decreases n
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type casting for n-1 in recursive call and assertions */
proof fn triangle_monotonic(m: nat, n: nat)
    requires m <= n
    ensures triangle(m) <= triangle(n)
    decreases n - m
{
    if m == n {
        // trivial
    } else {
        triangle_monotonic(m, (n-1) as nat);
        assert(triangle(n) == n + triangle((n-1) as nat));
        assert(triangle((n-1) as nat) <= triangle(n));
    }
}
// </vc-helpers>

// <vc-spec>
fn tail_triangle(n: u32, idx: u32, sum: &mut u32)

    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,

    ensures
        *sum == triangle(n as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): kept implementation from iteration 4 since errors were in helper */
{
    let mut idx = idx;
    while idx < n
        invariant
            idx <= n,
            *sum == triangle(idx as nat),
            *sum < 0x1_0000_0000
        decreases n - idx
    {
        let next_idx = idx + 1;
        proof {
            triangle_monotonic(next_idx as nat, n as nat);
            assert(triangle(next_idx as nat) <= triangle(n as nat));
            assert(triangle(n as nat) < 0x1_0000_0000);
            assert(triangle(next_idx as nat) < 0x1_0000_0000);
        }
        *sum = *sum + next_idx;
        idx = next_idx;
    }
}
// </vc-code>

}
fn main() {}