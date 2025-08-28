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
fn modmul(a: u32, b: u32, p: u32) -> (mul: u32)
    by (nonlinear_arith)
    requires
        p > 0,
    ensures
        mul == ((a as int) * (b as int)) % (p as int),
{
    (((a as u64) * (b as u64)) % (p as u64)) as u32
}

proof fn modp_rec_lemma(n: nat, p: nat)
    requires p > 0
    ensures modp_rec(n, p) == if n == 0 { 1nat % p } else { (modp_rec((n - 1) as nat, p) * 2) % p }
{
}

proof fn modp_base_case(p: nat)
    requires p > 0
    ensures modp_rec(0, p) == 1nat % p
{
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
    let mut result: u32 = 1 % p;
    let mut i: u32 = 0;
    
    proof {
        assert(modp_rec(0, p as nat) == 1nat % (p as nat));
        assert(result == modp_rec(i as nat, p as nat));
    }
    
    while i < n
        invariant
            p > 0,
            i <= n,
            result == modp_rec(i as nat, p as nat),
        decreases n - i,
    {
        let prev_result = result;
        result = modmul(result, 2, p);
        i = i + 1;
        
        proof {
            assert(modp_rec((i - 1) as nat, p as nat) == prev_result);
            assert(result == (prev_result * 2) % (p as int));
            assert(modp_rec(i as nat, p as nat) == (modp_rec((i - 1) as nat, p as nat) * 2) % (p as nat));
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}