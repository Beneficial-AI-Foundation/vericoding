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
    /* code modified by LLM (iteration 2): Initialize ret to 1 % p to satisfy initial invariant */
    let mut ret = 1u32 % p;
    let mut i = 0u32;
    
    while i < n
        invariant
            i <= n,
            p > 0,
            ret == modp_rec(i as nat, p as nat),
            ret < p,
        decreases n - i
    {
        ret = ((ret as u64 * 2) % (p as u64)) as u32;
        i = i + 1;
    }
    ret
}
// </vc-code>

}
fn main() {}