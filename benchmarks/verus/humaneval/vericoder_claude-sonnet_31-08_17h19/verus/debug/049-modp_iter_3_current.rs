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
proof fn modp_rec_properties(n: nat, p: nat)
    requires p > 0
    ensures modp_rec(n, p) < p
    decreases n
{
    if n == 0 {
        assert(1nat % p < p);
    } else {
        modp_rec_properties((n - 1) as nat, p);
        let prev = modp_rec((n - 1) as nat, p);
        assert(prev < p);
        assert((prev * 2) % p < p);
    }
}

proof fn modp_rec_base_case(p: nat)
    requires p > 0
    ensures modp_rec(0, p) == 1nat % p
{
}

proof fn modp_rec_step(n: nat, p: nat)
    requires p > 0, n > 0
    ensures modp_rec(n, p) == (modp_rec((n - 1) as nat, p) * 2) % p
{
}

proof fn modp_loop_invariant_helper(i: nat, n: nat, p: nat, result: nat)
    requires 
        p > 0,
        i <= n,
        result == modp_rec(i, p)
    ensures 
        result < p
{
    modp_rec_properties(i, p);
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
    let mut result = 1u32;
    let mut i = 0u32;
    
    proof {
        modp_rec_properties(0, p as nat);
        assert(1nat % (p as nat) == modp_rec(0, p as nat));
    }
    
    while i < n
        invariant
            p > 0,
            i <= n,
            result < p,
            result == modp_rec(i as nat, p as nat)
        decreases n - i
    {
        proof {
            modp_rec_properties(i as nat, p as nat);
            assert(result == modp_rec(i as nat, p as nat));
            assert(result < p);
        }
        
        result = (result * 2) % p;
        i = i + 1;
        
        proof {
            assert(i > 0);
            assert(modp_rec(i as nat, p as nat) == (modp_rec((i - 1) as nat, p as nat) * 2) % (p as nat));
            modp_rec_properties(i as nat, p as nat);
        }
    }
    
    proof {
        assert(i == n);
        assert(result == modp_rec(n as nat, p as nat));
    }
    
    result
}
// </vc-code>

fn main() {}
}