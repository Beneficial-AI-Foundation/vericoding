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
// Added helper lemmas to relate u64-mod results to nat-mod and to handle the multiply-by-2 case.
proof fn u64_mod_cast_to_nat(x: u64, y: u64)
    requires
        y > 0
    ensures
        ((x % y) as nat) == ((x as nat) % (y as nat))
{
    // Let xr = x % y, then xr < y, and casting preserves value.
    let xr: u64 = x % y;
    let xr_nat: nat = xr as nat;
    let x_nat: nat = x as nat;
    let y_nat: nat = y as nat;
    // By definition of modulus, xr_nat == x_nat % y_nat
    assert(xr_nat == x_nat % y_nat);
    assert(((x % y) as nat) == xr_nat);
}

proof fn lemma_mul2_mod(a: u32, p: u32)
    requires
        p > 0
    ensures
        (((a as u64 * 2) % (p as u64)) as nat) == ((a as nat * 2) % (p as nat))
{
    u64_mod_cast_to_nat((a as u64) * 2, p as u64);
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
    let mut r: u32 = 1 % p;
    let mut i: u32 = 0;
    while i < n
        invariant
            p > 0,
            i <= n,
            (r as nat) == modp_rec(i as nat, p as nat)
        decreases (n as nat) - (i as nat)
    {
        let old_r = r;
        let old_i = i;
        // Use u64 for the intermediate multiplication to avoid wrapping,
        // then reduce modulo p and cast back to u32.
        r = (((old_r as u64 * 2) % (p as u64)) as u32);
        i = i + 1;
        proof {
            // loop invariant before the update
            assert((old_r as nat) == modp_rec(old_i as nat, p as nat));
            // unfold the spec for the next index
            assert(modp_rec((old_i + 1) as nat, p as nat) == ((modp_rec(old_i as nat, p as nat) * 2) % (p as nat)));
            // combine to relate with old_r
            assert(modp_rec((old_i + 1) as nat, p as nat) == ((old_r as nat * 2) % (p as nat)));
            // relate the concrete update to the u64-level modulo result
            assert((r as nat) == (((old_r as u64 * 2) % (p as u64)) as nat));
            // use lemma to convert the u64-mod result to nat-mod
            lemma_mul2_mod(old_r, p);
            // conclude the desired equality
            assert((r as nat) == ((old_r as nat * 2) % (p as nat)));
            // finish establishing the invariant for the updated i
            assert((r as nat) == modp_rec(i as nat, p as nat));
        }
    }
    r
}
// </vc-code>

fn main() {}
}