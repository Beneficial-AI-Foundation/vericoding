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
    let mut result: u32 = 1u32 % p;
    let mut count: u32 = 0;
    while count < n
        invariant
            count <= n,
            result == modp_rec(count as nat, p as nat),
        decreases (n - count)
    {
        let temp = ((result as u64) * 2) % (p as u64);
        result = temp as u32;
        count = count + 1;
    }
    result
}
// </vc-code>

}
fn main() {}