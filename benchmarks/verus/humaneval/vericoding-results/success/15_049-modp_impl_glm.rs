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
    let mut result = 1 % p;
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result == modp_rec(i as nat, p as nat),
        decreases n - i,
    {
        let wide_result = result as u64;
        let wide_p = p as u64;
        result = ((wide_result * 2) % wide_p) as u32;
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}