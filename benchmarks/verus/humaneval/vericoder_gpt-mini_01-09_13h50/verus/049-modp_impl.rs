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
proof fn modp_rec_bound(n: nat, p: nat)
    requires p > 0
    ensures modp_rec(n, p) < p
{
    if n == 0 {
        // modp_rec(0,p) == 1 % p
        assert(modp_rec(0, p) == 1 % p);
        // For p > 0, 1 % p < p
        assert(1 % p < p);
        assert(modp_rec(0, p) < p);
    } else {
        modp_rec_bound(n - 1, p);
        // modp_rec(n,p) == (modp_rec(n-1,p) * 2) % p
        assert(modp_rec(n, p) == (modp_rec(n - 1, p) * 2) % p);
        // For any a and p>0, (a * 2) % p < p
        assert((modp_rec(n - 1, p) * 2) % p < p);
        assert(modp_rec(n, p) < p);
    }
}

proof fn modp_rec_step_cast(i: nat, p: nat)
    requires p > 0 && p <= (u32::MAX as nat)
    ensures ((modp_rec(i, p) as u32 * 2u32) % (p as u32)) == modp_rec(i + 1, p) as u32
{
    // By definition
    assert(modp_rec(i + 1, p) == (modp_rec(i, p) * 2) % p);

    // Bound modp_rec(i,p) < p, so it fits in u32
    modp_rec_bound(i, p);
    assert(modp_rec(i, p) < p);

    let a_nat: nat = modp_rec(i, p);
    // From a_nat < p and p <= u32::MAX, we have a_nat <= u32::MAX
    assert(a_nat <= (u32::MAX as nat));
    // cast equality: (a as u32) as nat == a
    assert((a_nat as u32) as nat == a_nat);

    // Now relate modular arithmetic between nat and u32 under these casts.
    // ((a as u32) * 2u32) % (p as u32) == ((a * 2) % p) as u32
    assert(((a_nat as u32) * 2u32) % (p as u32) == ((a_nat * 2) % p) as u32);

    // Combine with modp_rec(i+1,p) equality
    assert(((modp_rec(i, p) as u32) * 2u32) % (p as u32) == modp_rec(i + 1, p) as u32);
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
    let mut i: u32 = 0;
    let mut r: u32 = 1 % p;
    let mut r_nat: nat = 1 % (p as nat);
    let p_nat: nat = p as nat;

    proof {
        // bring preconditions into scope for proofs
        assert(p > 0);
        assert(p_nat > 0);
        assert(p_nat <= (u32::MAX as nat));
        // initial invariant holds: r_nat == modp_rec(0, p)
        assert(r_nat == modp_rec(0, p_nat));
        // r_nat fits in u32
        assert(r_nat <= (u32::MAX as nat));
        assert(r == r_nat as u32);
    }

    while i < n
        invariant (i as nat) <= (n as nat)
        invariant r_nat == modp_rec(i as nat, p_nat)
        invariant r == r_nat as u32
        decreases (n as nat) - (i as nat)
    {
        proof {
            // re-establish p bounds for lemma
            assert(p_nat > 0);
            assert(p_nat <= (u32::MAX as nat));
            // use lemma to relate nat-step to u32-step
            modp_rec_step_cast(i as nat, p_nat);
            // from r_nat == modp_rec(i,p) and lemma, derive the next-step relation as u32
            assert(((r_nat as u32) * 2u32) % p == modp_rec((i + 1) as nat, p_nat) as u32);
            // use r == r_nat as u32 invariant to replace
            assert(r == r_nat as u32);
            assert(((r * 2u32) % p) == modp_rec((i + 1) as nat, p_nat) as u32);
        }
        r = (r * 2u32) % p;
        r_nat = (r_nat * 2) % p_nat;
        i = i + 1;
    }
    r
}
// </vc-code>

fn main() {}
}