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
// pure-end

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn modp(n: u32, p: u32) -> (r: u32)
    by (nonlinear_arith)
    // pre-conditions-start
    requires
        p > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        r == modp_rec(n as nat, p as nat),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: u64 = 1;
    let p_u64 = p as u64;
    let n_nat = n as nat;
    let p_nat = p as nat;
    for i in 0..n
        invariant
            0 <= i <= n,
            result == modp_rec(i as nat, p_nat) as u64,
    {
        result = (result * 2) % p_u64;
    }
    // post
    assert(result == modp_rec(n_nat, p_nat) as u64);
    assert(result <= 0xFFFFFFFFu64);
    result as u32
}
// </vc-code>

fn main() {}
}