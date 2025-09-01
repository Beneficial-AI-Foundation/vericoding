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
#[verifier::loop_isolation(false)]
proof fn lemma_modp_rec_is_pow2_mod_p(n: nat, p: nat)
    requires
        p > 0,
    ensures
        modp_rec(n, p) == (2u64.pow(n as u32) % p as u64) as nat,
    decreases n,
{
    if n == 0 {
        assert(modp_rec(0, p) == 1nat % p);
        assert(2u64.pow(0) == 1);
        assert(1u64 % p as u64 == 1nat % p as nat);
    } else {
        lemma_modp_rec_is_pow2_mod_p((n - 1) as nat, p);
        let lhs = modp_rec(n, p);
        let rhs = (2u64.pow(n as u32) % p as u64) as nat;
        assert(modp_rec((n - 1) as nat, p) == (2u64.pow((n - 1) as u32) % p as u64) as nat);
        assert(lhs == (modp_rec((n - 1) as nat, p) * 2) % p);
        assert((2u64.pow((n - 1) as u32) % p as u64) as nat * 2 % p == (2u64.pow(n as u32) % p as u64) as nat) by(nonlinear_arith)
        {
            let n_minus_1_pow2_mod_p: u64 = 2u64.pow((n-1) as u32) % p as u64;
            assert( (n_minus_1_pow2_mod_p as nat * 2) % p == (2u64.pow(n as u32) % p as u64) as nat);
            assert((n_minus_1_pow2_mod_p * 2) % p as u64 == (2u64.pow(n as u32) % p as u64)) by(nonlinear_arith);
        }
    }
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
    // impl-start
    let mut i: u32 = 0;
    let mut res: u64 = 1;

    let p_u64 = p as u64;

    while i < n
        invariant
            i <= n,
            res == (2u64.pow(i) % p_u64),
            p_u64 == p as u64,
            p > 0,
    {
        res = (res * 2) % p_u64;
        i = i + 1;
    }
    assert(res == (2u64.pow(n) % p_u64));
    assert(res as nat == (2u64.pow(n as u32) % p as u64) as nat) by(nonlinear_arith);

    proof {
        lemma_modp_rec_is_pow2_mod_p(n as nat, p as nat);
    }
    assert(modp_rec(n as nat, p as nat) == (2u64.pow(n as u32) % p as u64) as nat);
    assert(res as nat == modp_rec(n as nat, p as nat));

    res as u32
    // impl-end
}
// </vc-code>

fn main() {}
}