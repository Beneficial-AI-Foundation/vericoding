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
    requires p > 0
    ensures ((modp_rec(i, p) as u32 * 2u32) % (p as u32)) == modp_rec(i + 1, p) as u32
{
    // By definition
    assert(modp_rec(i + 1, p) == (modp_rec(i, p) * 2) % p);

    // Bound modp_rec(i,p) < p, so it fits in u32
    modp_rec_bound(i, p);
    assert(modp_rec(i, p) < p);

    // Now reason about casts: since modp_rec(i,p) < p <= u32::MAX, the cast to u32 is exact.
    // Show that ((a as u32)*2 % p) corresponds to ((a*2)%p) as u32 for a = modp_rec(i,p).
    let a_nat: nat = modp_rec(i, p);
    // cast equalities
    assert((a_nat as u32) as nat == a_nat);
    // Use definition of integer % both on nat and on u32; these correspond under casts when divisors are the same positive value.
    // Conclude the required equality.
    assert(((a_nat as u32) * 2u32) % (p as u32) == ((a_nat * 2) % p) as u32);
    // Combine with modp_rec(i+1,p) equality
    assert(((modp_rec(i, p) as u32) * 2u32) % (p as u32) == modp_rec(i + 1, p) as u32);
}
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
    // impl-start
    let mut i: u32 = 0;
    let mut r: u32 = 1 % p;
    while i < n
        invariant i <= n
        invariant r == modp_rec(i as nat, p as nat) as u32
        decreases (n - i) as nat
    {
        proof {
            // use lemma to show next-step relation
            modp_rec_step_cast(i as nat, p as nat);
            assert(((r * 2u32) % p) == modp_rec((i + 1) as nat, p as nat) as u32);
        }
        r = (r * 2u32) % p;
        i = i + 1;
    }
    r
    // impl-end
}
// </vc-code>

fn main() {}
}