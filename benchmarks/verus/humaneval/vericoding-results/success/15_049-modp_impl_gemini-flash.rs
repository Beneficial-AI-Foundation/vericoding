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
/* helper modified by LLM (iteration 3): Simplified to directly reflect modp_rec behavior */
spec fn power_of_2_mod_p(n: nat, p: nat) -> nat
    decreases n,
{
    if n == 0 {
        1nat % p
    } else {
        (2 * power_of_2_mod_p((n - 1) as nat, p)) % p
    }
}
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
    let mut res: u32 = 1 % p;

    while i < n
        invariant
            i <= n,
            res as nat == modp_rec(i as nat, p as nat),
            0 < p,
        decreases n - i,
    {
        i = i + 1;
        res = ((res as u64 * 2) % p as u64) as u32;
    }
    res
}
// </vc-code>

}
fn main() {}