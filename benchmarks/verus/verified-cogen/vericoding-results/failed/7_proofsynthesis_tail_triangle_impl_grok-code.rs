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
/* helper modified by LLM (iteration 4): proved triangle_add lemma with assert using the recursive definition */
proof fn triangle_add(n: nat)
    ensures triangle((n+1) as nat) == triangle(n) + (n+1) as nat
{
    assert(triangle((n+1) as nat) == ((n+1) as nat + triangle(n)));
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
    /* code modified by LLM (iteration 4): added intermediary assert in proof to connect the lemma ensures */
{
    let mut i = idx;
    while i < n
        invariant
            i <= n,
            *sum == triangle(i as nat),
        decreases n - i,
    {
        *sum += (i + 1) as u32;
        i += 1;
        proof {
            triangle_add((i - 1) as nat);
            assert((*sum as nat) == triangle((i - 1) as nat) + i);
            assert((*sum as nat) == triangle(i as nat));
        }
    }
}
// </vc-code>

}
fn main() {}