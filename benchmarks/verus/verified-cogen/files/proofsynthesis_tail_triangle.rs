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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}