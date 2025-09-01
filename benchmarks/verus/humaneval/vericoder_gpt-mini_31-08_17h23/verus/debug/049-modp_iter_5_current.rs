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
proof fn lemma_modp_rec_step(n: nat, p: nat)
    ensures modp_rec(n + 1, p) == (modp_rec(n, p) * 2) % p
{
    assert(modp_rec(n + 1, p) == (modp_rec(n, p) * 2) % p);
}

proof fn lemma_modp_rec_range(n: nat, p: nat)
    requires p > 0
    ensures modp_rec(n, p) < p
{
    if n == 0 {
        assert(modp_rec(0, p) == 1 % p);
        assert(1 % p < p);
    } else {
        assert(modp_rec(n, p) == (modp_rec(n - 1, p) * 2) % p);
        lemma_modp_rec_range(n - 1, p);
        assert((modp_rec(n - 1, p) * 2) % p < p);
    }
}

proof fn lemma_u64_mod_eq_nat(a: u64, p: u64)
    requires
        p > 0,
        (a as nat) < (p as nat)
    ensures
        (((a * 2u64) % p) as nat) == ((a as nat) * 2) % (p as nat)
{
    // ((a * 2) as nat) == (a as nat) * 2
    assert(((a * 2u64) as nat) == (a as nat) * 2);
    // modulo on u64 casted to nat equals modulo on nat
    assert((((a * 2u64) % p) as nat) == ((a * 2u64) as nat) % (p as nat));
    // combine
    assert((((a * 2u64) % p) as nat) == ((a as nat) * 2) % (p as nat));
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
    let mut acc: u64 = 1u64 % (p as u64);

    while i < n
        invariant { i <= n }
        invariant { (acc as nat) == modp_rec(i as nat, p as nat) }
        decreases { (n - i) as nat }
    {
        let new_u64: u64 = ((acc * 2u64) % (p as u64));
        proof {
            assert((acc as nat) == modp_rec(i as nat, p as nat));
            // p > 0 is a precondition of the function
            assert(p > 0);
            lemma_modp_rec_range(i as nat, p as nat);
            assert((acc as nat) < (p as nat));
            lemma_u64_mod_eq_nat(acc, p as u64);
            lemma_modp_rec_step(i as nat, p as nat);
            assert((new_u64 as nat) == ((acc as nat) * 2) % (p as nat));
            assert((new_u64 as nat) == modp_rec((i as nat) + 1, p as nat));
        }
        acc = new_u64;
        i = i + 1;
    }

    acc as u32
}
// </vc-code>

fn main() {}
}