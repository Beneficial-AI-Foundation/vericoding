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
    lemma_pow2_mod_property(i, p);
}

proof fn lemma_mod_arithmetic(a: nat, p: nat)
    requires
        p > 0,
    ensures
        (a * 2) % p == ((a % p) * 2) % p,
{
    assert((a * 2) % p == ((a % p) * 2) % p) by {
        assert(a % p <= a);
        assert(a == (a / p) * p + (a % p));
        assert(a * 2 == (a / p) * p * 2 + (a % p) * 2);
        assert((a * 2) % p == ((a % p) * 2) % p);
    };
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
            r as nat == modp_rec(i as nat, p as nat),
        decreases n - i,
    {
        proof {
            lemma_pow2_iterative(n as nat, p as nat, r as nat, i as nat);
            lemma_mod_arithmetic(r as nat, p as nat);
        }
        let prev_r = r;
        r = (r * 2) % p;
        proof {
            assert(prev_r as nat == modp_rec(i as nat, p as nat));
            assert(r as nat == ((prev_r as nat) * 2) % (p as nat));
            assert(r as nat == modp_rec((i + 1) as nat, p as nat)) by {
                reveal(modp_rec);
            };
        }
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