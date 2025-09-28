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
/* helper modified by LLM (iteration 2): lemma: triangle(n+1) = triangle(n) + (n+1) */
proof fn triangle_succ(n: nat)
    ensures triangle(n + 1) == triangle(n) + (n + 1)
{
    assert(triangle(n + 1) == (n + 1) + triangle(n));
    assert((n + 1) + triangle(n) == triangle(n) + (n + 1));
}

/* helper modified by LLM (iteration 2): lemma: monotonicity of triangle wrt <= */
proof fn triangle_mono_le(m: nat, n: nat)
    requires m <= n
    ensures triangle(m) <= triangle(n)
    decreases n - m
{
    if m == n {
    } else {
        assert(m < n);
        triangle_succ(m);
        assert(triangle(m + 1) == triangle(m) + (m + 1));
        assert(triangle(m) <= triangle(m) + (m + 1));
        triangle_mono_le(m + 1, n);
        assert(triangle(m + 1) <= triangle(n));
        assert(triangle(m) <= triangle(n));
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
{
    /* code modified by LLM (iteration 2): added loop decreases and explicit arithmetic/proof steps for update */
    let mut i = idx;
    while i < n
        invariant
            idx <= i <= n,
            *sum == triangle(i as nat),
            triangle(i as nat) <= triangle(n as nat),
        decreases (n - i) as nat
    {
        let next = i + 1;
        let old_sum = *sum;
        assert((old_sum as nat) + (next as nat) < 0x1_0000_0000) by {
            triangle_succ(i as nat);
            assert((old_sum as nat) == triangle(i as nat));
            assert((old_sum as nat) + (next as nat) == triangle((i as nat) + 1));
            assert((i as nat) + 1 <= n as nat);
            triangle_mono_le((i as nat) + 1, n as nat);
            assert(triangle((i as nat) + 1) <= triangle(n as nat));
            assert(triangle(n as nat) < 0x1_0000_0000);
        };
        proof {
            assert(i < n);
            assert(((n - (i + 1)) as nat) < ((n - i) as nat));
        }
        *sum = old_sum + next;
        proof {
            triangle_succ(i as nat);
            assert((next as nat) == (i as nat) + 1);
            assert((*sum as nat) == (old_sum as nat) + (next as nat));
            assert((old_sum as nat) == triangle(i as nat));
            assert((*sum as nat) == triangle((i as nat) + 1));
        }
        i = next;
        assert(*sum == triangle(i as nat));
        proof {
            triangle_mono_le(i as nat, n as nat);
        }
    }
    assert(i == n);
    assert(*sum == triangle(n as nat));
}
// </vc-code>

}
fn main() {}