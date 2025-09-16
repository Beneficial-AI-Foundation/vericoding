// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn modp_rec(n: nat, p: nat) -> (result:nat)
    decreases n,
{
    if n == 0 {
        1nat % p
    } else {
        (modp_rec((n - 1) as nat, p) * 2) % p
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn modp(n: u32, p: u32) -> (r: u32)
    by (nonlinear_arith)

    requires
        p > 0,

    ensures
        r == modp_rec(n as nat, p as nat),
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0;
    let mut r: u32 = 1 % p;

    while i < n
        invariant
            p > 0,
            i <= n,
            r < p,
            r == modp_rec(i as nat, p as nat),
        decreases n - i
    {
        r = (((r as u64) * 2) % (p as u64)) as u32;
        i = i + 1;
    }

    r
}
// </vc-code>

}
fn main() {}