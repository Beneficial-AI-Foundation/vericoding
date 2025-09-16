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
/* helper modified by LLM (iteration 5): prove recursive relation of modp_rec */
proof fn modp_rec_step(k: nat, p: nat)
    requires
        p > 0,
    ensures
        modp_rec(k + 1, p) == (modp_rec(k, p) * 2) % p,
    decreases
        k,
{
    if k == 0 {
        assert(modp_rec(1 as nat, p) == (modp_rec(0 as nat, p) * 2) % p);
    } else {
        modp_rec_step((k - 1) as nat, p);
        assert(modp_rec(k + 1, p) == (modp_rec(k, p) * 2) % p);
    }
}

/* helper modified by LLM (iteration 5): prove modp_rec is always less than p */
proof fn modp_rec_lt(k: nat, p: nat)
    requires
        p > 0,
    ensures
        modp_rec(k, p) < p,
    decreases
        k,
{
    if k == 0 {
        assert(modp_rec(0 as nat, p) == 1nat % p);
        assert(modp_rec(0 as nat, p) < p);
    } else {
        modp_rec_lt((k - 1) as nat, p);
        modp_rec_step((k - 1) as nat, p);
        assert(modp_rec(k, p) == (modp_rec((k - 1) as nat, p) * 2) % p);
        assert((modp_rec((k - 1) as nat, p) * 2) % p < p);
        assert(modp_rec(k, p) < p);
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
    /* code modified by LLM (iteration 5): implement iterative doubling modulo p with proof using helpers */
    let mut i: u32 = 0;
    let mut acc: u32 = 1 % p;
    while i < n
        invariant
            (i as nat) <= (n as nat),
            acc as nat == modp_rec(i as nat, p as nat),
        decreases
            (n as nat - i as nat)
    {
        let old_i = i;
        let old_acc = acc;
        let tmp64: u64 = (old_acc as u64) + (old_acc as u64);
        if tmp64 >= (p as u64) {
            acc = (tmp64 - (p as u64)) as u32;
        } else {
            acc = tmp64 as u32;
        }
        i += 1;
        proof {
            modp_rec_step(old_i as nat, p as nat);
            modp_rec_lt(old_i as nat, p as nat);
            assert(old_acc as nat == modp_rec(old_i as nat, p as nat));
            assert((old_acc as nat * 2nat) == tmp64 as nat);
            if tmp64 >= (p as u64) {
                assert(acc as nat == ((old_acc as nat * 2nat) - (p as nat)));
            } else {
                assert(acc as nat == (old_acc as nat * 2nat));
            }
            assert(acc as nat == ((old_acc as nat * 2nat) % (p as nat)));
            assert(acc as nat == modp_rec((old_i as nat) + 1, p as nat));
        }
    }
    acc
}
// </vc-code>

}
fn main() {}