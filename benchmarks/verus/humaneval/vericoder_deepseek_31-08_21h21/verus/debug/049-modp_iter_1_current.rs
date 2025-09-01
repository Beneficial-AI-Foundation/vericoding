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
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1nat
    } else {
        2 * pow2((n - 1) as nat)
    }
}

proof fn lemma_pow2_mod_property(n: nat, p: nat)
    requires
        p > 0,
    ensures
        pow2(n) % p == modp_rec(n, p),
    decreases n,
{
    if n == 0 {
        reveal(modp_rec);
    } else {
        lemma_pow2_mod_property((n - 1) as nat, p);
        reveal(modp_rec);
    }
}

proof fn lemma_pow2_iterative(n: nat, p: nat, acc: nat, i: nat)
    requires
        p > 0,
        i <= n,
        acc == pow2(i) % p,
    ensures
        acc == modp_rec(i, p),
    decreases n - i,
{
    if i < n {
        lemma_pow2_mod_property(i, p);
        calc! {
            (==)
            acc * 2 % p;
            == { }
            (pow2(i) % p) * 2 % p;
            == { }
            (pow2(i) * 2) % p;
            == { reveal(pow2); }
            pow2(i + 1) % p;
            == { lemma_pow2_mod_property((i + 1) as nat, p); }
            modp_rec((i + 1) as nat, p);
        }
    } else {
        lemma_pow2_mod_property(i, p);
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
    let mut r: u32 = 1;
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            r == pow2(i as nat) % (p as nat),
        decreases n - i,
    {
        assert(r * 2 % p == pow2((i + 1) as nat) % (p as nat)) by {
            lemma_pow2_iterative(n as nat, p as nat, r as nat, i as nat);
        }
        r = (r * 2) % p;
        i += 1;
    }
    proof {
        lemma_pow2_iterative(n as nat, p as nat, r as nat, i as nat);
    }
    r
}
// </vc-code>

fn main() {}
}