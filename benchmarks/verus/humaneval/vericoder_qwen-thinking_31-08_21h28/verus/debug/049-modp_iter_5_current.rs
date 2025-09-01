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
    let mut result = 1 % p;
    let mut i = 0;
    while i < n
        decreases n as nat - i as nat
        invariant (result as nat) == modp_rec((i as nat), (p as nat))
    {
        let double = (result as u64) * 2;
        result = (double % (p as u64)) as u32;
        i = i + 1;
        assert((result as nat) == modp_rec((i as nat), (p as nat)));
    }
    result
}
// </vc-code>

fn main() {}
}