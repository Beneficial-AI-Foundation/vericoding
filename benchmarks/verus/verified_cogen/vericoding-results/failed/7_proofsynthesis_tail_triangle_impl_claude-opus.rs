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
proof fn triangle_monotonic(n: nat, m: nat)
    requires m <= n
    ensures triangle(m) <= triangle(n)
    decreases n - m
{
    if m == n {
        assert(triangle(m) == triangle(n));
    } else {
        reveal(triangle);
        triangle_monotonic((n - 1) as nat, m);
        assert(triangle(n) == n + triangle((n - 1) as nat));
        assert(triangle(m) <= triangle((n - 1) as nat));
        assert(triangle(m) <= triangle(n));
    }
}

/* helper modified by LLM (iteration 5): fixed type errors in monotonicity lemma */
proof fn triangle_step(n: nat, idx: nat, sum: nat)
    requires
        idx <= n,
        sum == triangle(idx),
        triangle(n) < 0x1_0000_0000,
    ensures
        sum + (idx + 1) == triangle((idx + 1) as nat),
        triangle((idx + 1) as nat) < 0x1_0000_0000,
    decreases n - idx
{
    reveal(triangle);
    assert(triangle((idx + 1) as nat) == (idx + 1) + triangle(idx));
    triangle_monotonic(n, (idx + 1) as nat);
    assert(triangle((idx + 1) as nat) <= triangle(n));
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
{
    /* code modified by LLM (iteration 5): implementation with correct proof */
    let mut i = idx;
    while i < n
        invariant
            i <= n,
            *sum == triangle(i as nat),
            triangle(n as nat) < 0x1_0000_0000,
            triangle(i as nat) < 0x1_0000_0000,
        decreases n - i
    {
        i = i + 1;
        proof {
            triangle_step(n as nat, (i - 1) as nat, *sum as nat);
            assert(*sum == triangle((i - 1) as nat));
            assert(*sum + i == triangle(i as nat));
        }
        *sum = *sum + i;
    }
}
// </vc-code>

}
fn main() {}