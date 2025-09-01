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
    let mut result: u64 = (1 % (p as u64));
    let mut i: u32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            p > 0,
            (result as nat) == modp_rec(i as nat, p as nat),
            (result as int) < (p as int),
        decreases n - i,
    {
        assert(i < n);
        result = ((result * 2) % (p as u64));
        i = i + 1;
    }
    (result as u32)
}
// </vc-code>

fn main() {}
}