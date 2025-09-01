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
proof fn lemma_modp_rec_step(n: nat, p: nat)
    ensures modp_rec(n + 1, p) == (modp_rec(n, p) * 2) % p
{
    // For any n, n+1 != 0, so by definition of modp_rec:
    assert(modp_rec(n + 1, p) == (modp_rec(n, p) * 2) % p);
}

proof fn lemma_modp_rec_range(n: nat, p: nat)
    requires p > 0
    ensures modp_rec(n, p) < p
{
    if n == 0 {
        // modp_rec(0, p) == 1 % p, and for p>0, 1 % p < p
        assert(modp_rec(0, p) == 1 % p);
        assert(1 % p < p);
    } else {
        // modp_rec(n, p) == (modp_rec(n-1, p) * 2) % p
        assert(modp_rec(n, p) == (modp_rec(n - 1, p) * 2) % p);
        lemma_modp_rec_range(n - 1, p);
        // remainder modulo p is always < p
        assert((modp_rec(n - 1, p) * 2) % p < p);
    }
}

proof fn lemma_u64_mod_eq_nat(a: u32, p: u32)
    requires p > 0
    requires (a as nat) < (p as nat)
    ensures (((a as u64) * 2u64) % (p as u64)) as nat == ((a as nat) * 2) % (p as nat)
{
    // Casts preserve values; perform modular arithmetic equivalence via casts
    assert((a as u64) as nat == a as nat);
    assert((p as u64) as nat == p as nat);
    // Multiply in u64 equals multiply in nat (since values small enough)
    assert(((a as u64) * 2u64) as nat == (a as nat) * 2);
    // Now modulo with u64 then cast to nat equals nat modulo
    assert((((a as u64) * 2u64) % (p as u64)) as nat == ((a as nat) * 2) % (p as nat));
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
// <vc-code>
{
    // impl-start
    let mut i: u32 = 0;
    let mut acc: u32 = 1 % p;

    while i < n
        invariant i <= n
        invariant (acc as nat) == modp_rec(i as nat, p as nat)
        decreases (n - i) as nat
    {
        // compute new accumulator safely using u64 to avoid u32 overflow
        let new_u64: u64 = ((acc as u64) * 2u64) % (p as u64);
        proof {
            // acc corresponds to modp_rec(i, p) by the invariant
            assert((acc as nat) == modp_rec(i as nat, p as nat));
            // modp_rec(i,p) < p
            lemma_modp_rec_range(i as nat, p as nat);
            // therefore acc < p (as nat)
            assert((acc as nat) < (p as nat));
            // relate u64 modulo to nat modulo
            lemma_u64_mod_eq_nat(acc, p);
            // by lemma_modp_rec_step, modp_rec(i+1,p) == (modp_rec(i,p)*2)%p
            lemma_modp_rec_step(i as nat, p as nat);
            // combine equalities to show new_u64 as nat equals modp_rec(i+1,p)
            assert((new_u64 as nat) == ((acc as nat) * 2) % (p as nat));
            assert((new_u64 as nat) == modp_rec((i as nat) + 1, p as nat));
        }
        acc = new_u64 as u32;
        i = i + 1;
    }

    acc
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}