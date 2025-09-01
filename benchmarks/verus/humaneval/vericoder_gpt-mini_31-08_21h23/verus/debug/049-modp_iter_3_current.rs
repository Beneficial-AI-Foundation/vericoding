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
// No helpers needed for this proof.
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
    let mut r: u32 = 1 % p;
    let mut i: u32 = 0;
    while i < n
        decreases (n as nat) - (i as nat)
        invariant {
            p > 0,
            i <= n,
            (r as nat) == modp_rec(i as nat, p as nat)
        }
    {
        let old_r = r;
        let old_i = i;
        r = (r.wrapping_mul(2)) % p;
        i = i + 1;
        proof {
            // from the loop invariant before the update
            assert((old_r as nat) == modp_rec(old_i as nat, p as nat));
            // unfold the specification for the next index
            assert(modp_rec((old_i + 1) as nat, p as nat) == ((modp_rec(old_i as nat, p as nat) * 2) % (p as nat)));
            // combine the two equalities
            assert(modp_rec((old_i + 1) as nat, p as nat) == ((old_r as nat * 2) % (p as nat)));
            // relate the concrete update to the nat-level arithmetic
            assert((r as nat) == ((old_r as nat * 2) % (p as nat)));
            // conclude the invariant for the updated i
            assert((r as nat) == modp_rec(i as nat, p as nat));
        }
    }
    r
}
// </vc-code>

fn main() {}
}