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
proof fn modp_rec_unfold(n: nat, p: nat)
    requires p > 0,
    ensures 
        n == 0 ==> modp_rec(n, p) == 1nat % p,
        n > 0 ==> modp_rec(n, p) == (modp_rec((n - 1) as nat, p) * 2) % p,
{
    reveal(modp_rec);
}

proof fn lemma_modp_iter(i: nat, n: nat, p: nat, ret: nat)
    requires 
        p > 0,
        i <= n,
        ret == modp_rec(i, p),
    ensures
        i < n ==> (ret * 2) % p == modp_rec((i + 1) as nat, p),
    decreases n - i,
{
    if i < n {
        modp_rec_unfold((i + 1) as nat, p);
        assert((i + 1) - 1 == i);
    }
}

proof fn lemma_modp_bound(n: nat, p: nat)
    requires p > 0,
    ensures modp_rec(n, p) < p,
    decreases n,
{
    if n == 0 {
        modp_rec_unfold(n, p);
        assert(modp_rec(n, p) == 1nat % p);
        assert(1nat % p < p);
    } else {
        modp_rec_unfold(n, p);
        lemma_modp_bound((n - 1) as nat, p);
        assert(modp_rec((n - 1) as nat, p) < p);
        assert(modp_rec(n, p) == (modp_rec((n - 1) as nat, p) * 2) % p);
        assert((modp_rec((n - 1) as nat, p) * 2) % p < p);
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
    let mut ret: u32 = 1 % p;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            p > 0,
            i <= n,
            ret == modp_rec(i as nat, p as nat),
            ret < p,
        decreases n - i,
    {
        proof {
            lemma_modp_iter(i as nat, n as nat, p as nat, ret as nat);
            lemma_modp_bound((i + 1) as nat, p as nat);
            assert(ret < p);
            assert(ret * 2 <= (p - 1) * 2);
            assert((p - 1) * 2 < u32::MAX);
        }
        i = i + 1;
        ret = (ret * 2) % p;
    }
    
    ret
}
// </vc-code>

fn main() {}
}