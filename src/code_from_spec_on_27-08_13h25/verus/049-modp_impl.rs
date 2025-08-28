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
fn modmul(a: u32, b: u32, p: u32) -> (mul: u32)
    by (nonlinear_arith)
    requires
        p > 0,
    ensures
        mul == ((a as int) * (b as int)) % (p as int),
{
    (((a as u64) * (b as u64)) % (p as u64)) as u32
}

proof fn modp_rec_helper(i: nat, p: nat)
    by (nonlinear_arith)
    requires
        p > 0,
    ensures
        modp_rec(i, p) < p,
    decreases i,
{
    if i == 0 {
        assert(modp_rec(0, p) == 1nat % p);
        assert(1nat % p < p);
    } else {
        modp_rec_helper((i - 1) as nat, p);
        assert(modp_rec(i, p) == (modp_rec((i - 1) as nat, p) * 2) % p);
        assert((modp_rec((i - 1) as nat, p) * 2) % p < p);
    }
}

proof fn modp_rec_step(i: nat, p: nat)
    by (nonlinear_arith)
    requires
        p > 0,
        i > 0,
    ensures
        modp_rec(i, p) == (modp_rec((i - 1) as nat, p) * 2) % p,
{
}
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
    let mut result: u32 = 1;
    let mut i: u32 = 0;

    while i < n
        invariant
            i <= n,
            p > 0,
            result as nat == modp_rec(i as nat, p as nat),
        decreases n - i,
    {
        proof {
            modp_rec_step((i + 1) as nat, p as nat);
        }
        result = modmul(result, 2, p);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}