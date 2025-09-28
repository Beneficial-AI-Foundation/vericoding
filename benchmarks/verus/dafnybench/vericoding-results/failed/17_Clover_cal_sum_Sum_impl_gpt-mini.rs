use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
    let N: nat = n as nat;
    let mut i: nat = 0;
    let mut s_nat: nat = 0;
    while i < N
        invariant i <= N
        invariant s_nat == i * (i + 1) / 2
        decreases N - i
    {
        i = i + 1;
        s_nat = s_nat + i;
        assert(s_nat == i * (i + 1) / 2);
    }
    let s: u32 = s_nat as u32;
    s
}
// </vc-code>

fn main() {}

}