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
    // pre-conditions-start
    requires
        p > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        mul == ((a as int) * (b as int)) % (p as int),
    // post-conditions-end
{
    // impl-start
    (((a as u64) * (b as u64)) % (p as u64)) as u32
    // impl-end
}

proof fn modp_rec_relation(n: nat, p: nat)
    by (nonlinear_arith)
    requires
        p > 0,
        n > 0,
    ensures
        modp_rec(n, p) == (modp_rec((n - 1) as nat, p) * 2) % p,
{
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn modp_iter_equiv(i: nat, n: nat, p: nat, acc: nat)
    by (nonlinear_arith)
    requires
        p > 0,
        acc == modp_rec(i, p),
        i <= n,
    ensures
        modp_rec(n, p) == if i == n { acc } else { (acc * pow2((n - i) as nat)) % p },
    decreases n - i,
{
    if i < n {
        modp_iter_equiv(i + 1, n, p, (acc * 2) % p);
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
    // impl-start
    let mut i: u32 = 0;
    let mut acc: u32 = 1 % p;
    
    while i < n
        invariant
            p > 0,
            i <= n,
            acc == modp_rec(i as nat, p as nat),
        decreases n - i,
    {
        acc = modmul(acc, 2, p);
        i = i + 1;
        
        proof {
            modp_rec_relation(i as nat, p as nat);
        }
    }
    
    acc
    // impl-end
}
// </vc-code>

}
fn main() {}